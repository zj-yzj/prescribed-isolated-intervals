import Formalization.GenericLabels
import Formalization.MomentSetLevelPackaging

/-!
# Instances of the abstract label-family construction

The original positional labels and the polynomial-size finite moment labels
both satisfy `BoundedLabelSeparation`. Consequently both concrete set-level
theorems are instances of the generic construction.
-/

namespace IntervalBases

theorem linearLabelValue_positionalLabel {m M B : Nat}
    (coefficients : Fin m -> Int) :
    linearLabelValue (fun index : Fin m => positionalLabel M B index.val) coefficients =
      scaledPositionalValue M B (List.ofFn coefficients) := by
  rw [linearLabelValue, scaledPositionalValue, positionalValue_ofFn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  simp only [positionalLabel]
  push_cast
  ring

/-- Positional power labels satisfy the abstract separation interface. -/
theorem positionalLabel_boundedLabelSeparation {m M B L : Nat}
    (hbase : L <= B) :
    BoundedLabelSeparation
      (fun index : Fin m => positionalLabel M B index.val) L M := by
  intro xs ys hne hnorm
  have hlistNe : Not (List.ofFn xs = List.ofFn ys) := by
    intro heq
    apply hne
    exact List.ofFn_injective heq
  have hlistNorm :
      l1Norm (List.ofFn xs) + l1Norm (List.ofFn ys) <= B := by
    rw [l1Norm_ofFn, l1Norm_ofFn]
    exact hnorm.trans hbase
  simpa [linearLabelValue_positionalLabel] using
    scale_le_natAbs_sub_scaledPositionalValue
      (M := M) (B := B) (xs := List.ofFn xs) (ys := List.ofFn ys)
      (by simp) hlistNe hlistNorm

/-- The positional-label set-level theorem recovered from the abstract label
family theorem. -/
theorem constructedBasis_has_isolated_exceptional_pattern_via_generic
    {targets : List Int} {h M B T d : Nat}
    (hh : 2 <= h) (htarget : ∀ index, (targets.get index).natAbs <= T)
    (hbase : 2 * ((h - 1) * h) <= B) (hbudget : 2 * (h * T) + d <= M) :
    (∀ index : Fin targets.length,
      targets.get index ∈ hFoldSumset (constructedBasis h M B targets) h) ∧
    (∀ x ∈ hFoldSumset (constructedBasis h M B targets) h,
      x ∉ prescribedTargets targets ->
        ∀ index : Fin targets.length, d <= (x - targets.get index).natAbs) ∧
    (∀ x ∈ hFoldSumset (constructedBasis h M B targets) h,
      x ∉ prescribedTargets targets ->
        ∀ y ∈ hFoldSumset (constructedBasis h M B targets) h,
          x ≠ y -> d <= (x - y).natAbs) := by
  simpa [genericConstructedBasis, constructedBasis] using
    genericConstructedBasis_has_isolated_exceptional_pattern
      hh htarget (positionalLabel_boundedLabelSeparation hbase) hbudget

theorem linearLabelValue_scaledMomentLabel {m M L Q : Nat}
    (coefficients : Fin m -> Int) :
    linearLabelValue
      (fun index : Fin m => scaledMomentLabel M L Q index.val) coefficients =
        (M : Int) * momentLabelValue L Q coefficients := by
  rw [linearLabelValue, momentLabelValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  simp only [scaledMomentLabel]
  ring

/-- Finite moment labels satisfy the abstract separation interface. -/
theorem scaledMomentLabel_boundedLabelSeparation {m M L Q order : Nat}
    (horder : order <= L) (hbase : momentEncodingBase m L <= Q) :
    BoundedLabelSeparation
      (fun index : Fin m => scaledMomentLabel M L Q index.val) order M := by
  intro xs ys hne hnorm
  rw [linearLabelValue_scaledMomentLabel, linearLabelValue_scaledMomentLabel]
  exact scale_le_natAbs_sub_scaledMomentLabelValue hbase hne (hnorm.trans horder)

/-- The moment-label set-level theorem recovered from the abstract label
family theorem. -/
theorem momentConstructedBasis_has_isolated_exceptional_pattern_via_generic
    {targets : List Int} {h M L Q T d : Nat}
    (hh : 2 <= h) (htarget : ∀ index, (targets.get index).natAbs <= T)
    (horder : 2 * ((h - 1) * h) <= L)
    (hbase : momentEncodingBase targets.length L <= Q)
    (hbudget : 2 * (h * T) + d <= M) :
    (∀ index : Fin targets.length,
      targets.get index ∈ hFoldSumset (momentConstructedBasis h M L Q targets) h) ∧
    (∀ x ∈ hFoldSumset (momentConstructedBasis h M L Q targets) h,
      x ∉ prescribedTargets targets ->
        ∀ index : Fin targets.length, d <= (x - targets.get index).natAbs) ∧
    (∀ x ∈ hFoldSumset (momentConstructedBasis h M L Q targets) h,
      x ∉ prescribedTargets targets ->
        ∀ y ∈ hFoldSumset (momentConstructedBasis h M L Q targets) h,
          x ≠ y -> d <= (x - y).natAbs) := by
  simpa [genericConstructedBasis, momentConstructedBasis] using
    genericConstructedBasis_has_isolated_exceptional_pattern
      hh htarget (scaledMomentLabel_boundedLabelSeparation horder hbase) hbudget

end IntervalBases
