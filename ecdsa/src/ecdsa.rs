use super::integer::{IntegerChip, IntegerConfig};
use crate::halo2;
use crate::integer;
use crate::maingate;
use ecc::maingate::RegionCtx;
use ecc::{AssignedPoint, EccConfig, GeneralEccChip};
use halo2::arithmetic::CurveAffine;
use halo2::halo2curves::ff::PrimeField;
use halo2::{circuit::Value, plonk::Error};
use integer::rns::Integer;
use integer::{AssignedInteger, IntegerInstructions};
use maingate::{AssignedCondition, MainGateConfig, RangeConfig};

#[derive(Clone, Debug)]
pub struct EcdsaConfig {
    pub main_gate_config: MainGateConfig,
    pub range_config: RangeConfig,
}

impl EcdsaConfig {
    pub fn new(range_config: RangeConfig, main_gate_config: MainGateConfig) -> Self {
        Self {
            range_config,
            main_gate_config,
        }
    }

    pub fn ecc_chip_config(&self) -> EccConfig {
        EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }

    pub fn integer_chip_config(&self) -> IntegerConfig {
        IntegerConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }
}

#[derive(Clone, Debug)]
pub struct EcdsaSig<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    pub r: Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    pub s: Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

pub struct AssignedEcdsaSig<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    pub r: AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    pub s: AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

pub struct AssignedPublicKey<
    W: PrimeField,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    pub point: AssignedPoint<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

pub struct EcdsaChip<
    E: CurveAffine,
    N: PrimeField,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
>(GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>);

impl<E: CurveAffine, N: PrimeField, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>
    EcdsaChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
{
    pub fn new(ecc_chip: GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>) -> Self {
        Self(ecc_chip)
    }

    pub fn scalar_field_chip(
        &self,
    ) -> &IntegerChip<E::ScalarExt, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        self.0.scalar_field_chip()
    }

    fn ecc_chip(&self) -> GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        self.0.clone()
    }
}

impl<E: CurveAffine, N: PrimeField, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>
    EcdsaChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
{
    pub fn verify(
        &self,
        ctx: &mut RegionCtx<'_, N>,
        sig: &AssignedEcdsaSig<E::Scalar, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        pk: &AssignedPublicKey<E::Base, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        msg_hash: &AssignedInteger<E::Scalar, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        enable_skipping_invalid_signature: bool,
    ) -> Result<AssignedCondition<N>, Error> {
        let ecc_chip = self.ecc_chip();
        let scalar_chip = ecc_chip.scalar_field_chip();
        let base_chip = ecc_chip.base_field_chip();

        // 1. check 0 < r, s < n, if r == 0 or s == 0 the signature is marked as invalid

        // since `assert_not_zero` already includes a in-field check, we can just
        // call `assert_not_zero`
        let is_r_valid = scalar_chip.is_not_zero(ctx, &sig.r)?;
        let is_s_valid = scalar_chip.is_not_zero(ctx, &sig.s)?;
        let is_r_s_valid = scalar_chip.and(ctx, &is_r_valid, &is_s_valid)?;

        // 2. w = s^(-1) (mod n)
        let (s_inv, _) = scalar_chip.invert(ctx, &sig.s)?;

        // 3. u1 = m' * w (mod n)
        let u1 = scalar_chip.mul(ctx, msg_hash, &s_inv)?;

        // 4. u2 = r * w (mod n)
        let u2 = scalar_chip.mul(ctx, &sig.r, &s_inv)?;

        // 5. compute Q = u1*G + u2*pk
        let e_gen = ecc_chip.assign_point(ctx, Value::known(E::generator()))?;
        let pairs = vec![(e_gen, u1), (pk.point.clone(), u2)];
        let q = ecc_chip.mul_batch_1d_horizontal(ctx, pairs, 4)?;

        // 6. reduce q_x in E::ScalarExt
        // assuming E::Base/E::ScalarExt have the same number of limbs
        let q_x = q.x();
        let (q_x_reduced_in_q, is_q_x_reduced_in_q_valid) = base_chip.reduce(ctx, q_x)?;
        let (q_x_reduced_in_r, is_q_x_reduced_in_r_valid) = scalar_chip.reduce_external(ctx, &q_x_reduced_in_q)?;
        let is_q_x_reduced_valid = scalar_chip.and(ctx, &is_q_x_reduced_in_q_valid, &is_q_x_reduced_in_r_valid)?;

        // 7. check if Q.x == r (mod n)
        let is_q_x_reduced_in_r_equal_to_r = scalar_chip.is_strict_equal(ctx, &q_x_reduced_in_r, &sig.r)?;
        
        // 8. check if both is_r_s_valid and is_q_x_reduced_in_r_equal_to_r are true to determine overall validity
        let is_valid = scalar_chip.and(ctx, &is_q_x_reduced_in_r_equal_to_r, &is_r_s_valid)?;
        let is_valid = scalar_chip.and(ctx, &is_valid, &is_q_x_reduced_valid)?;
        let enable_skipping_invalid_signature = scalar_chip.assign_constant(ctx, (enable_skipping_invalid_signature as u64).into())?;
        let enable_skipping_invalid_signature = scalar_chip.is_not_zero(ctx, &enable_skipping_invalid_signature)?;
        scalar_chip.one_or_one(ctx, &enable_skipping_invalid_signature, &is_valid)?;

        Ok(is_valid)
    }
}

#[cfg(test)]
mod tests {
    use super::{AssignedEcdsaSig, AssignedPublicKey, EcdsaChip};
    use crate::halo2;
    use crate::integer;
    use crate::maingate;
    use ecc::integer::Range;
    use ecc::maingate::big_to_fe;
    use ecc::maingate::fe_to_big;
    use ecc::maingate::RegionCtx;
    use ecc::{EccConfig, GeneralEccChip};
    use halo2::arithmetic::CurveAffine;
    use halo2::circuit::{Layouter, SimpleFloorPlanner, Value};
    use halo2::halo2curves::{
        ff::{Field, FromUniformBytes, PrimeField},
        group::{Curve, Group},
    };
    use halo2::plonk::{Circuit, ConstraintSystem, Error};
    use integer::IntegerInstructions;
    use maingate::mock_prover_verify;
    use maingate::{MainGate, MainGateConfig, RangeChip, RangeConfig, RangeInstructions};
    use rand_core::OsRng;

    use std::fmt::{Debug};
    use std::marker::PhantomData;

    const BIT_LEN_LIMB: usize = 68;
    const NUMBER_OF_LIMBS: usize = 4;

    #[derive(Clone, Debug)]
    struct TestCircuitEcdsaVerifyConfig {
        main_gate_config: MainGateConfig,
        range_config: RangeConfig,
    }

    impl TestCircuitEcdsaVerifyConfig {
        pub fn new<C: CurveAffine, N: PrimeField>(meta: &mut ConstraintSystem<N>) -> Self {
            let (rns_base, rns_scalar) =
                GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::rns();
            let main_gate_config = MainGate::<N>::configure(meta);
            let mut overflow_bit_lens: Vec<usize> = vec![];
            overflow_bit_lens.extend(rns_base.overflow_lengths());
            overflow_bit_lens.extend(rns_scalar.overflow_lengths());
            let composition_bit_lens = vec![BIT_LEN_LIMB / NUMBER_OF_LIMBS];

            let range_config = RangeChip::<N>::configure(
                meta,
                &main_gate_config,
                composition_bit_lens,
                overflow_bit_lens,
            );
            TestCircuitEcdsaVerifyConfig {
                main_gate_config,
                range_config,
            }
        }

        pub fn ecc_chip_config(&self) -> EccConfig {
            EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
        }

        pub fn config_range<N: PrimeField>(
            &self,
            layouter: &mut impl Layouter<N>,
        ) -> Result<(), Error> {
            let range_chip = RangeChip::<N>::new(self.range_config.clone());
            range_chip.load_table(layouter)?;

            Ok(())
        }
    }

    #[derive(Default, Clone)]
    struct TestCircuitEcdsaVerify<E: CurveAffine, N: PrimeField> {
        public_key: Value<E>,
        signature: Value<(E::Scalar, E::Scalar)>,
        msg_hash: Value<E::Scalar>,

        aux_generator: E,
        window_size: usize,

        valid_input: bool,
        enable_skipping_invalid_signature: bool,

        _marker: PhantomData<N>,
    }

    impl<E: CurveAffine, N: PrimeField> Circuit<N> for TestCircuitEcdsaVerify<E, N> {
        type Config = TestCircuitEcdsaVerifyConfig;
        type FloorPlanner = SimpleFloorPlanner;
        #[cfg(feature = "circuit-params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
            TestCircuitEcdsaVerifyConfig::new::<E, N>(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<N>,
        ) -> Result<(), Error> {
            let mut ecc_chip = GeneralEccChip::<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(
                config.ecc_chip_config(),
            );

            layouter.assign_region(
                || "assign aux values",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);

                    ecc_chip.assign_aux_generator(ctx, Value::known(self.aux_generator))?;
                    ecc_chip.assign_aux(ctx, self.window_size, 2)?;
                    Ok(())
                },
            )?;

            let ecdsa_chip = EcdsaChip::new(ecc_chip.clone());
            let scalar_chip = ecc_chip.scalar_field_chip();

            layouter.assign_region(
                || "region 0",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);

                    let is_valid = scalar_chip.assign_constant(ctx, (true as u64).into())?;
                    let is_valid = scalar_chip.is_not_zero(ctx, &is_valid)?;

                    let r = self.signature.map(|signature| signature.0);
                    let s = self.signature.map(|signature| signature.1);

                    let integer_r = if self.valid_input {
                        ecc_chip.new_unassigned_scalar(r.clone())
                    } else {
                        let max_reminder = scalar_chip.rns().max_remainder.clone();
                        ecc_chip.new_unassigned_big(max_reminder)
                    };
                    let integer_s = ecc_chip.new_unassigned_scalar(s);
                    let msg_hash = ecc_chip.new_unassigned_scalar(self.msg_hash);

                    let (r_assigned, is_assigned_integer_succeeded ) =
                        scalar_chip.try_assign_integer(ctx, integer_r, Range::Remainder)?;
                    let is_valid = scalar_chip.and(ctx, &is_valid, &is_assigned_integer_succeeded)?;
                    let (s_assigned, is_assigned_integer_succeeded) =
                        scalar_chip.try_assign_integer(ctx, integer_s, Range::Remainder)?;
                    let is_valid = scalar_chip.and(ctx, &is_valid, &is_assigned_integer_succeeded)?;
                    let sig = AssignedEcdsaSig {
                        r: r_assigned,
                        s: s_assigned,
                    };

                    let point = self.public_key.map(|point| ecc_chip.to_rns_point(point));
                    let (x, y) = point
                        .map(|point| (point.x().clone(), point.y().clone()))
                        .unzip();
                    let (pk_in_circuit, is_pk_on_curve) = ecc_chip.assign_x_y(ctx, x.into(), y.into())?;
                    let is_valid = scalar_chip.and(ctx, &is_valid, &is_pk_on_curve)?;

                    let enable_skipping_invalid_signature = scalar_chip.assign_constant(ctx, (self.enable_skipping_invalid_signature as u64).into())?;
                    let enable_skipping_invalid_signature = scalar_chip.is_not_zero(ctx, &enable_skipping_invalid_signature)?;
                    scalar_chip.one_or_one(ctx, &enable_skipping_invalid_signature, &is_valid)?;

                    let pk_assigned = AssignedPublicKey {
                        point: pk_in_circuit,
                    };
                    let msg_hash = scalar_chip.assign_integer(ctx, msg_hash, Range::Remainder)?;
                    let response = ecdsa_chip.verify(ctx, &sig, &pk_assigned, &msg_hash, self.enable_skipping_invalid_signature);
                    return response;
                },
            )?;

            config.config_range(&mut layouter)?;

            Ok(())
        }
    }

    #[test]
    fn test_ecdsa_verifier() {
        fn mod_n<C: CurveAffine>(x: C::Base) -> C::Scalar {
            let x_big = fe_to_big(x);
            big_to_fe(x_big)
        }

        fn generate_valid_inputs<C: CurveAffine, N: FromUniformBytes<64> + Ord>() -> (C, C::Scalar, C::Scalar, C::Scalar) {
            let g = C::generator();

            // Generate a key pair
            let sk = <C as CurveAffine>::ScalarExt::random(OsRng);
            let public_key = (g * sk).to_affine();

            // Generate a valid signature
            // Suppose `m_hash` is the message hash
            let msg_hash = <C as CurveAffine>::ScalarExt::random(OsRng);

            // Draw arandomness
            let k = <C as CurveAffine>::ScalarExt::random(OsRng);
            let k_inv = k.invert().unwrap();

            // Calculate `r`
            let r_point = (g * k).to_affine().coordinates().unwrap();
            let x = r_point.x();
            let r = mod_n::<C>(*x);

            // Calculate `s`
            let s = k_inv * (msg_hash + (r * sk));

            // Sanity check. Ensure we construct a valid signature. So lets verify it
            {
                let s_inv = s.invert().unwrap();
                let u_1 = msg_hash * s_inv;
                let u_2 = r * s_inv;
                let r_point = ((g * u_1) + (public_key * u_2))
                    .to_affine()
                    .coordinates()
                    .unwrap();
                let x_candidate = r_point.x();
                let r_candidate = mod_n::<C>(*x_candidate);
                assert_eq!(r, r_candidate);
            }
            (public_key, r, s, msg_hash)
        }

        fn generate_invalid_inputs<C: CurveAffine, N: FromUniformBytes<64> + Ord>() -> (C, C::Scalar, C::Scalar, C::Scalar) {
            let (public_key, r, _, msg_hash) = generate_valid_inputs::<C, N>();
            (public_key, r, r, msg_hash)
        }

        fn run<C: CurveAffine, N: FromUniformBytes<64> + Ord>(valid_input: bool, enable_skipping_invalid_signature: bool) {
            let (public_key, r, s, msg_hash) = if valid_input {
                generate_valid_inputs::<C, N>()
            } else {
                generate_invalid_inputs::<C, N>()
            };

            let aux_generator = C::CurveExt::random(OsRng).to_affine();
            let circuit = TestCircuitEcdsaVerify::<C, N> {
                public_key: Value::known(public_key),
                signature: Value::known((r.clone(), s.clone())),
                msg_hash: Value::known(msg_hash),
                aux_generator,
                window_size: 4,
                valid_input,
                enable_skipping_invalid_signature,
                ..Default::default()
            };
            let instance = vec![vec![]];
            let result = mock_prover_verify(&circuit, instance);
            if valid_input || enable_skipping_invalid_signature {
                assert_eq!(result, Ok(()));
            } else {
                assert!(result.is_err());
            }
        }

        use crate::curves::bn256::Fr as BnScalar;
        use crate::curves::pasta::{Fp as PastaFp, Fq as PastaFq};
        use crate::curves::secp256k1::Secp256k1Affine as Secp256k1;
        
        // Return Errors
        run::<Secp256k1, BnScalar>(false, false);
        run::<Secp256k1, PastaFp>(false, false);
        run::<Secp256k1, PastaFq>(false, false);

        run::<Secp256k1, BnScalar>(false, true);
        run::<Secp256k1, PastaFp>(false, true);
        run::<Secp256k1, PastaFq>(false, true);

        run::<Secp256k1, BnScalar>(true, false);
        run::<Secp256k1, PastaFp>(true, false);
        run::<Secp256k1, PastaFq>(true, false);

        run::<Secp256k1, BnScalar>(true, true);
        run::<Secp256k1, PastaFp>(true, true);
        run::<Secp256k1, PastaFq>(true, true);
    }
}
