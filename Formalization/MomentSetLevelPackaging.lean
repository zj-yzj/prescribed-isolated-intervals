import Formalization.SetLevelPackaging
import Formalization.MomentRepresentation

/-!
# Set-level isolation for finite moment labels

This file packages the polynomial-diameter moment-label construction. The
combinatorial uniqueness argument is reused from the positional-label
formalization; only the arithmetic separation interface changes.
-/

namespace IntervalBases

theorem labelCoefficients_eq_of_labelCoefficient_eq {targets : List Int} {h : Nat}
    {generators otherGenerators : List (SignedGenerator targets)}
    (hcoefficients :
      labelCoefficient h generators = labelCoefficient h otherGenerators) :
    labelCoefficients h generators = labelCoefficients h otherGenerators := by
  simp only [labelCoefficients, hcoefficients]

theorem labelCoefficients_eq_replicate_zero_of_labelCoefficient_eq_zero
    {targets : List Int} {h : Nat} {generators : List (SignedGenerator targets)}
    (hzero : labelCoefficient h generators = 0) :
    labelCoefficients h generators = List.replicate targets.length 0 := by
  apply labelCoefficients_eq_replicate_zero_iff.mpr
  intro index
  exact congrFun hzero index

/-- Equal nonzero count coefficient functions determine the same exceptional
sum, even when the tagged terms occur in a different order. -/
theorem sum_momentGeneratorValue_eq_of_labelCoefficient_eq_of_ne_zero
    {targets : List Int} {h M L Q : Nat} (hh : 1 <= h)
    (generators otherGenerators : List (SignedGenerator targets))
    (hlength : generators.length = h) (hotherLength : otherGenerators.length = h)
    (hcoefficients :
      labelCoefficient h generators = labelCoefficient h otherGenerators)
    (hnonzero : Not (labelCoefficient h generators = 0)) :
    (generators.map (SignedGenerator.momentValue h M L Q)).sum =
      (otherGenerators.map (SignedGenerator.momentValue h M L Q)).sum := by
  have hcoefficientLists :
      labelCoefficients h generators = labelCoefficients h otherGenerators :=
    labelCoefficients_eq_of_labelCoefficient_eq hcoefficients
  have htotal :
      (Finset.univ.sum fun index =>
        positiveCount generators index + negativeCount generators index) = h := by
    rw [sum_positiveCount_add_negativeCount, hlength]
  have hotherTotal :
      (Finset.univ.sum fun index =>
        positiveCount otherGenerators index + negativeCount otherGenerators index) = h := by
    rw [sum_positiveCount_add_negativeCount, hotherLength]
  have hbalance :
      ∀ index,
        (h - 1) * positiveCount generators index + negativeCount otherGenerators index =
          (h - 1) * positiveCount otherGenerators index + negativeCount generators index :=
    count_balance_of_labelCoefficients_eq hh hcoefficientLists
  have hnotMatched :
      Not (∀ index, negativeCount generators index =
        (h - 1) * positiveCount generators index) := by
    intro hmatched
    apply hnonzero
    funext index
    have hzeroList :=
      labelCoefficients_eq_replicate_zero_of_negativeCount_eq_mul_positiveCount hh hmatched
    exact labelCoefficients_eq_replicate_zero_iff.mp hzeroList index
  have hotherNotMatched :
      Not (∀ index, negativeCount otherGenerators index =
        (h - 1) * positiveCount otherGenerators index) := by
    intro hmatched
    apply hnonzero
    rw [hcoefficients]
    funext index
    have hzeroList :=
      labelCoefficients_eq_replicate_zero_of_negativeCount_eq_mul_positiveCount hh hmatched
    exact labelCoefficients_eq_replicate_zero_iff.mp hzeroList index
  have hpositive :
      positiveCount generators = positiveCount otherGenerators :=
    positiveCounts_eq_of_coefficient_eq_of_not_matched hh
      (positiveCount generators) (negativeCount generators)
      (positiveCount otherGenerators) (negativeCount otherGenerators)
      htotal hotherTotal hbalance hnotMatched hotherNotMatched
  have hoffset :
      representationOffset generators = representationOffset otherGenerators := by
    rw [← sum_positiveCount_mul_target_eq_representationOffset,
      ← sum_positiveCount_mul_target_eq_representationOffset, hpositive]
  have hlabel :
      momentRepresentationLabelValue h M L Q generators =
        momentRepresentationLabelValue h M L Q otherGenerators := by
    rw [momentRepresentationLabelValue_eq_scaledMomentLabelValue,
      momentRepresentationLabelValue_eq_scaledMomentLabelValue, hcoefficients]
  rw [sum_momentGeneratorValue_eq_offset_add_labelValue,
    sum_momentGeneratorValue_eq_offset_add_labelValue, hoffset, hlabel]

/-- Distinct coefficient functions of two exact `h`-term representations
give moment-construction sums separated by at least `d`. -/
theorem gap_of_distinct_momentLabelCoefficients
    {targets : List Int} {h M L Q T d : Nat}
    (hh : 2 <= h) (htarget : ∀ index, (targets.get index).natAbs <= T)
    (horder : 2 * ((h - 1) * h) <= L)
    (hbase : momentEncodingBase targets.length L <= Q)
    (hbudget : 2 * (h * T) + d <= M)
    (generators otherGenerators : List (SignedGenerator targets))
    (hlength : generators.length = h) (hotherLength : otherGenerators.length = h)
    (hne : Not (labelCoefficient h generators =
      labelCoefficient h otherGenerators)) :
    d <= ((generators.map (SignedGenerator.momentValue h M L Q)).sum -
      (otherGenerators.map (SignedGenerator.momentValue h M L Q)).sum).natAbs := by
  have hnorm :
      functionL1Norm (labelCoefficient h generators) +
        functionL1Norm (labelCoefficient h otherGenerators) <= L := by
    have hleft := functionL1Norm_labelCoefficient_le hh generators
    have hright := functionL1Norm_labelCoefficient_le hh otherGenerators
    rw [hlength] at hleft
    rw [hotherLength] at hright
    omega
  have hoffset :
      (representationOffset generators - representationOffset otherGenerators).natAbs <=
        2 * (h * T) := by
    calc
      (representationOffset generators - representationOffset otherGenerators).natAbs <=
          (representationOffset generators).natAbs +
            (representationOffset otherGenerators).natAbs :=
        Int.natAbs_sub_le _ _
      _ <= generators.length * T + otherGenerators.length * T :=
        Nat.add_le_add (natAbs_representationOffset_le generators htarget)
          (natAbs_representationOffset_le otherGenerators htarget)
      _ = 2 * (h * T) := by rw [hlength, hotherLength]; ring
  rw [sum_momentGeneratorValue_eq_offset_add_labelValue,
    sum_momentGeneratorValue_eq_offset_add_labelValue,
    momentRepresentationLabelValue_eq_scaledMomentLabelValue,
    momentRepresentationLabelValue_eq_scaledMomentLabelValue]
  exact offset_gap_of_distinct_scaledMomentLabelValues
    hbase hne hnorm hoffset hbudget

/-- Every exceptional moment-construction sum is separated from every
prescribed target. -/
theorem momentExceptional_gap_from_target
    {targets : List Int} {h M L Q T d : Nat}
    (hh : 2 <= h) (htarget : ∀ index, (targets.get index).natAbs <= T)
    (horder : 2 * ((h - 1) * h) <= L)
    (hbase : momentEncodingBase targets.length L <= Q)
    (hbudget : 2 * (h * T) + d <= M)
    {x : Int} (hx : x ∈ hFoldSumset (momentConstructedBasis h M L Q targets) h)
    (hxExceptional : x ∉ prescribedTargets targets) (index : Fin targets.length) :
    d <= (x - targets.get index).natAbs := by
  obtain ⟨generators, hlength, hsum⟩ :=
    exists_moment_generator_list_of_mem_hFoldSumset hx
  have hnonzero : Not (labelCoefficient h generators = 0) := by
    intro hzero
    obtain ⟨targetIndex, htargetSum⟩ :=
      exists_target_eq_sum_momentGeneratorValue_of_labelCoefficients_eq_zero
        (by omega) generators hlength
          (labelCoefficients_eq_replicate_zero_of_labelCoefficient_eq_zero hzero)
    apply hxExceptional
    exact ⟨targetIndex, hsum ▸ htargetSum⟩
  have hnorm :
      functionL1Norm (labelCoefficient h generators) +
        functionL1Norm (0 : Fin targets.length -> Int) <= L := by
    have hzeroNorm : functionL1Norm (0 : Fin targets.length -> Int) = 0 := by
      simp [functionL1Norm]
    rw [hzeroNorm, add_zero]
    have hleft := functionL1Norm_labelCoefficient_le hh generators
    rw [hlength] at hleft
    omega
  have hoffset :
      (representationOffset generators - targets.get index).natAbs <= 2 * (h * T) := by
    calc
      (representationOffset generators - targets.get index).natAbs <=
          (representationOffset generators).natAbs + (targets.get index).natAbs :=
        Int.natAbs_sub_le _ _
      _ <= generators.length * T + T :=
        Nat.add_le_add (natAbs_representationOffset_le generators htarget) (htarget index)
      _ <= 2 * (h * T) := by rw [hlength]; nlinarith
  rw [← hsum, sum_momentGeneratorValue_eq_offset_add_labelValue,
    momentRepresentationLabelValue_eq_scaledMomentLabelValue]
  have hgap := offset_gap_of_distinct_scaledMomentLabelValues
    (xs := labelCoefficient h generators) (ys := (0 : Fin targets.length -> Int))
    (u := representationOffset generators) (v := targets.get index)
    (M := M) (L := L) (Q := Q) (R := 2 * (h * T)) (d := d)
    hbase hnonzero hnorm hoffset hbudget
  simpa [momentLabelValue] using hgap

/-- Distinct exceptional moment-construction sums are separated. -/
theorem momentExceptional_gap
    {targets : List Int} {h M L Q T d : Nat}
    (hh : 2 <= h) (htarget : ∀ index, (targets.get index).natAbs <= T)
    (horder : 2 * ((h - 1) * h) <= L)
    (hbase : momentEncodingBase targets.length L <= Q)
    (hbudget : 2 * (h * T) + d <= M)
    {x y : Int} (hx : x ∈ hFoldSumset (momentConstructedBasis h M L Q targets) h)
    (hy : y ∈ hFoldSumset (momentConstructedBasis h M L Q targets) h)
    (hxExceptional : x ∉ prescribedTargets targets) (hne : x ≠ y) :
    d <= (x - y).natAbs := by
  obtain ⟨generators, hlength, hsum⟩ :=
    exists_moment_generator_list_of_mem_hFoldSumset hx
  obtain ⟨otherGenerators, hotherLength, hotherSum⟩ :=
    exists_moment_generator_list_of_mem_hFoldSumset hy
  have hnonzero : Not (labelCoefficient h generators = 0) := by
    intro hzero
    obtain ⟨index, htargetSum⟩ :=
      exists_target_eq_sum_momentGeneratorValue_of_labelCoefficients_eq_zero
        (by omega) generators hlength
          (labelCoefficients_eq_replicate_zero_of_labelCoefficient_eq_zero hzero)
    apply hxExceptional
    exact ⟨index, hsum ▸ htargetSum⟩
  have hcoefficients :
      Not (labelCoefficient h generators = labelCoefficient h otherGenerators) := by
    intro heq
    apply hne
    rw [← hsum, ← hotherSum]
    exact sum_momentGeneratorValue_eq_of_labelCoefficient_eq_of_ne_zero
      (by omega) generators otherGenerators hlength hotherLength heq hnonzero
  rw [← hsum, ← hotherSum]
  exact gap_of_distinct_momentLabelCoefficients hh htarget horder hbase hbudget
    generators otherGenerators hlength hotherLength hcoefficients

/-- Set-level polynomial-diameter construction: every target occurs, while
all other sums are isolated from the target set and from each other. -/
theorem momentConstructedBasis_has_isolated_exceptional_pattern
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
  refine ⟨?_, ?_, ?_⟩
  · intro index
    exact target_mem_hFoldSumset_momentConstructedBasis targets (by omega) index
  · intro x hx hxExceptional index
    exact momentExceptional_gap_from_target hh htarget horder hbase hbudget
      hx hxExceptional index
  · intro x hx hxExceptional y hy hne
    exact momentExceptional_gap hh htarget horder hbase hbudget
      hx hy hxExceptional hne

end IntervalBases
