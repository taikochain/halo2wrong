use super::{IntegerChip, IntegerInstructions, Range};
use crate::rns::MaybeReduced;
use crate::{AssignedInteger, PrimeField};
use halo2::plonk::Error;
use maingate::{halo2, AssignedCondition, AssignedValue, MainGateInstructions, RangeInstructions, RegionCtx, Term};

impl<W: PrimeField, N: PrimeField, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>
    IntegerChip<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
{
    /// Reduces an [`AssignedInteger`] if any of its limbs values is greater
    /// than the [`Rns`] `max_unreduced_limb`.
    ///
    /// Panics if the value of the integer is greater than [`Rns`]
    /// `max_reducible_value`.
    pub(super) fn reduce_if_limb_values_exceeds_unreduced(
        &self,
        ctx: &mut RegionCtx<'_, N>,
        a: &AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    ) -> Result<AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>, Error> {
        let exceeds_max_limb_value = a
            .limbs
            .iter()
            .any(|limb| limb.max_val() > self.rns.max_unreduced_limb);
        {
            // Sanity check for completeness

            // Reduction quotient is limited upto a dense single limb. It is quite possible
            // to make it more than a single limb. However even single limb will
            // support quite amount of lazy additions and make reduction process
            // much easier.
            let max_reduction_quotient = self.rns.max_reduced_limb.clone();
            let max_reducible_value =
                max_reduction_quotient * &self.rns.wrong_modulus + &self.rns.max_remainder;
            assert!(a.max_val() < max_reducible_value);
        }
        if exceeds_max_limb_value {
            let result = self.reduce(ctx, a)?;
            Ok(result.0)
        } else {
            Ok(self.new_assigned_integer(a.limbs(), a.native().clone()))
        }
    }

    /// Try to reduces an [`AssignedInteger`] if any of its limbs values is greater
    /// than the [`Rns`] `max_unreduced_limb`.
    ///
    /// Panics if the value of the integer is greater than [`Rns`]
    /// `max_reducible_value`.
    pub(super) fn try_reduce(
        &self,
        ctx: &mut RegionCtx<'_, N>,
        a: &AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    ) -> Result<(AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>, AssignedCondition<N>), Error> {
        let main_gate = self.main_gate();

        let (a, is_reduce_if_limb_values_succeeded) = self.try_reduce_if_limb_values_exceeds_reduced(ctx, a)?;
        let (a, is_reduce_if_max_operand_value_succeeded) = self.try_reduce_if_max_operand_value_exceeds(ctx, &a)?;
        let is_reduce_succeeded = main_gate.and(ctx, &is_reduce_if_limb_values_succeeded, &is_reduce_if_max_operand_value_succeeded)?;

        Ok((a, is_reduce_succeeded))
    }

    /// Try to reduces an [`AssignedInteger`] if any of its limbs values is greater
    /// than the [`Rns`] `max_unreduced_limb`.
    ///
    /// Panics if the value of the integer is greater than [`Rns`]
    /// `max_reducible_value`.
    pub(super) fn try_reduce_if_limb_values_exceeds_reduced(
        &self,
        ctx: &mut RegionCtx<'_, N>,
        a: &AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    ) -> Result<(AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>, AssignedCondition<N>), Error> {
        let exceeds_max_limb_value = a
            .limbs
            .iter()
            .any(|limb| limb.max_val() > self.rns.max_reduced_limb);

        // Soft sanity check for completeness
        // Reduction quotient is limited upto a dense single limb. It is quite possible
        // to make it more than a single limb. However even single limb will
        // support quite amount of lazy additions and make reduction process
        // much easier.
        let max_reduction_quotient = self.rns.max_reduced_limb.clone();
        let max_reducible_value =
            max_reduction_quotient * &self.rns.wrong_modulus + &self.rns.max_remainder;
        let is_valid = self.assign_constant(ctx, ((a.max_val() < max_reducible_value) as u64).into())?;
        let is_valid = self.is_not_zero_without_reduce(ctx, &is_valid)?;

        if exceeds_max_limb_value {
            let (result, is_reduce_succeeded) = self.reduce(ctx, a)?;
            let is_valid = self.and(ctx, &is_valid, &is_reduce_succeeded)?;
            Ok((result, is_valid))
        } else {
            let zero = self.assign_constant(ctx, W::ZERO)?;
            let zero = self.is_strict_equal(ctx, &zero.clone(), &zero)?;
            Ok((self.new_assigned_integer(a.limbs(), a.native().clone()), zero))
        }
    }

    /// Reduces an [`AssignedInteger`] if any of its limbs values is greater
    /// than the [`Rns`] `max_reduced_limb`
    pub(super) fn reduce_if_limb_values_exceeds_reduced(
        &self,
        ctx: &mut RegionCtx<'_, N>,
        a: &AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    ) -> Result<AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>, Error> {
        let exceeds_max_limb_value = a
            .limbs
            .iter()
            .any(|limb| limb.max_val() > self.rns.max_reduced_limb);
        if exceeds_max_limb_value {
            let result = self.reduce(ctx, a)?;
            Ok(result.0)
        } else {
            Ok(self.new_assigned_integer(a.limbs(), a.native().clone()))
        }
    }

    /// Reduces an [`AssignedInteger`] if any of its max value is greater
    /// than the [`Rns`] `max_operand`.
    pub(super) fn reduce_if_max_operand_value_exceeds(
        &self,
        ctx: &mut RegionCtx<'_, N>,
        a: &AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    ) -> Result<AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>, Error> {
        let exceeds_max_value = a.max_val() > self.rns.max_operand;
        if exceeds_max_value {
            let result = self.reduce(ctx, a)?;
            Ok(result.0)
        } else {
            Ok(self.new_assigned_integer(a.limbs(), a.native().clone()))
        }
    }

    /// Try to reduces an [`AssignedInteger`] if any of its max value is greater
    /// than the [`Rns`] `max_operand`.
    pub(super) fn try_reduce_if_max_operand_value_exceeds(
        &self,
        ctx: &mut RegionCtx<'_, N>,
        a: &AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    ) -> Result<(AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>, AssignedCondition<N>), Error> {
        let exceeds_max_value = a.max_val() > self.rns.max_operand;

        // Soft sanity check for completeness
        // Reduction quotient is limited upto a dense single limb. It is quite possible
        // to make it more than a single limb. However even single limb will
        // support quite amount of lazy additions and make reduction process
        // much easier.
        let max_reduction_quotient = self.rns.max_reduced_limb.clone();
        let max_reducible_value =
            max_reduction_quotient * &self.rns.wrong_modulus + &self.rns.max_remainder;
        let is_valid = self.assign_constant(ctx, ((a.max_val() < max_reducible_value) as u64).into())?;
        let is_valid = self.is_not_zero_without_reduce(ctx, &is_valid)?;

        if exceeds_max_value {
            let (result, is_reduce_succeeded) = self.reduce(ctx, a)?;
            let is_valid = self.and(ctx, &is_valid, &is_reduce_succeeded)?;
            Ok((result, is_valid))
        } else {
            let zero = self.assign_constant(ctx, W::ZERO)?;
            let zero = self.is_strict_equal(ctx, &zero.clone(), &zero)?;
            Ok((self.new_assigned_integer(a.limbs(), a.native().clone()), zero))
        }
    }

    pub(super) fn reduce_generic(
        &self,
        ctx: &mut RegionCtx<'_, N>,
        a: &AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    ) -> Result<(AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>, AssignedCondition<N>), Error> {
        let main_gate = self.main_gate();
        let (zero, one) = (N::ZERO, N::ONE);

        let witness: MaybeReduced<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> =
            a.integer().as_ref().map(|a_int| a_int.reduce()).into();
        let quotient = witness.short();
        let result = witness.result();

        // Add soft check here
        // Apply ranges
        let range_chip = self.range_chip();

        // Change to try_assign_integer that has soft check
        let result = self.try_assign_integer(ctx, result.into(), Range::Remainder)?;

        let quotient = range_chip.assign(ctx, quotient, Self::sublimb_bit_len(), BIT_LEN_LIMB)?;
        let residues = witness
            .residues()
            .iter()
            .map(|v| range_chip.assign(ctx, *v, Self::sublimb_bit_len(), self.rns.red_v_bit_len))
            .collect::<Result<Vec<AssignedValue<N>>, Error>>()?;

        // Assign intermediate values
        let t: Vec<AssignedValue<N>> = a
            .limbs()
            .iter()
            .zip(self.rns.negative_wrong_modulus_decomposed.into_iter())
            .map(|(a_i, w_i)| {
                main_gate.compose(
                    ctx,
                    &[
                        Term::Assigned(a_i.as_ref(), one),
                        Term::Assigned(&quotient, w_i),
                    ],
                    zero,
                )
            })
            .collect::<Result<Vec<AssignedValue<N>>, Error>>()?;

        // Constrain binary part of crt
        self.constrain_binary_crt(
            ctx,
            &t.try_into()
                .expect("Unexpected failure in AssignedCell -> AssignedValue conversion"),
            &result.0,
            residues,
        )?;

        // Constrain native part of crt
        main_gate.assert_zero_sum(
            ctx,
            &[
                Term::Assigned(a.native(), -one),
                Term::Assigned(&quotient, self.rns.wrong_modulus_in_native_modulus),
                Term::Assigned(result.0.native(), one),
            ],
            zero,
        )?;

        Ok(result)
    }
}
