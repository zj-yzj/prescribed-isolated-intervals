import Formalization.ExceptionalCounts

/-!
# Set-level packaging of the explicit construction

This file combines the decoded tagged representations, count uniqueness, and
positional separation lemmas. The final theorem states that every prescribed
target occurs in the constructed `h`-fold sumset, while every other sum is
isolated from the targets and from every other exceptional sum.
-/

open scoped BigOperators

namespace IntervalBases

/-- The finite set of prescribed target points. In the paper this list is an
enumeration of the union of the desired intervals. -/
def prescribedTargets (targets : List Int) : Set Int :=
  {x | ∃ index : Fin targets.length, x = targets.get index}

/-- Equality of integer coefficient lists gives the natural-number balance
equations used by the exceptional-count uniqueness theorem. -/
theorem count_balance_of_labelCoefficients_eq {targets : List Int} {h : Nat}
    (hh : 1 <= h) {generators otherGenerators : List (SignedGenerator targets)}
    (hcoefficients : labelCoefficients h generators =
      labelCoefficients h otherGenerators) :
    ∀ index,
      (h - 1) * positiveCount generators index + negativeCount otherGenerators index =
        (h - 1) * positiveCount otherGenerators index + negativeCount generators index := by
  have hcoefficientFunctions :
      labelCoefficient h generators = labelCoefficient h otherGenerators := by
    apply List.ofFn_injective
    exact hcoefficients
  intro index
  have hindex := congrFun hcoefficientFunctions index
  simp only [labelCoefficient] at hindex
  have hcast : ((h : Int) - 1) = (h - 1 : Nat) := by
    omega
  rw [hcast] at hindex
  exact_mod_cast (sub_eq_sub_iff_add_eq_add.mp hindex)

/-- A common nonzero coefficient list determines the represented integer,
even if the tagged term lists use a different order. -/
theorem sum_generatorValue_eq_of_labelCoefficients_eq_of_ne_zero
    {targets : List Int} {h M B : Nat} (hh : 1 <= h)
    (generators otherGenerators : List (SignedGenerator targets))
    (hlength : generators.length = h) (hotherLength : otherGenerators.length = h)
    (hcoefficients : labelCoefficients h generators =
      labelCoefficients h otherGenerators)
    (hnonzero : labelCoefficients h generators ≠ List.replicate targets.length 0) :
    (generators.map (SignedGenerator.value h M B)).sum =
      (otherGenerators.map (SignedGenerator.value h M B)).sum := by
  have htotal :
      (∑ index, (positiveCount generators index + negativeCount generators index)) = h := by
    rw [sum_positiveCount_add_negativeCount, hlength]
  have hotherTotal :
      (∑ index,
        (positiveCount otherGenerators index + negativeCount otherGenerators index)) = h := by
    rw [sum_positiveCount_add_negativeCount, hotherLength]
  have hbalance :
      ∀ index,
        (h - 1) * positiveCount generators index + negativeCount otherGenerators index =
          (h - 1) * positiveCount otherGenerators index + negativeCount generators index :=
    count_balance_of_labelCoefficients_eq hh hcoefficients
  have hnotMatched :
      ¬ ∀ index, negativeCount generators index = (h - 1) * positiveCount generators index := by
    intro hmatched
    exact hnonzero
      (labelCoefficients_eq_replicate_zero_of_negativeCount_eq_mul_positiveCount hh hmatched)
  have hotherNonzero :
      labelCoefficients h otherGenerators ≠ List.replicate targets.length 0 := by
    rw [← hcoefficients]
    exact hnonzero
  have hotherNotMatched :
      ¬ ∀ index,
        negativeCount otherGenerators index = (h - 1) * positiveCount otherGenerators index := by
    intro hmatched
    exact hotherNonzero
      (labelCoefficients_eq_replicate_zero_of_negativeCount_eq_mul_positiveCount hh hmatched)
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
      representationLabelValue h M B generators =
        representationLabelValue h M B otherGenerators := by
    rw [representationLabelValue_eq_scaledPositionalValue_labelCoefficients,
      representationLabelValue_eq_scaledPositionalValue_labelCoefficients, hcoefficients]
  rw [sum_generatorValue_eq_offset_add_labelValue,
    sum_generatorValue_eq_offset_add_labelValue, hoffset, hlabel]

/-- Distinct coefficient vectors of two exact `h`-term representations give
represented integers separated by at least `d`. -/
theorem gap_of_distinct_labelCoefficients {targets : List Int} {h M B T d : Nat}
    (hh : 2 <= h) (htarget : ∀ index, (targets.get index).natAbs <= T)
    (hbase : 2 * ((h - 1) * h) <= B) (hbudget : 2 * (h * T) + d <= M)
    (generators otherGenerators : List (SignedGenerator targets))
    (hlength : generators.length = h) (hotherLength : otherGenerators.length = h)
    (hne : labelCoefficients h generators ≠ labelCoefficients h otherGenerators) :
    d <= ((generators.map (SignedGenerator.value h M B)).sum -
      (otherGenerators.map (SignedGenerator.value h M B)).sum).natAbs := by
  have hnorm :
      l1Norm (labelCoefficients h generators) +
        l1Norm (labelCoefficients h otherGenerators) <= B := by
    have hleft := l1Norm_labelCoefficients_le hh generators
    have hright := l1Norm_labelCoefficients_le hh otherGenerators
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
  rw [sum_generatorValue_eq_offset_add_labelValue,
    sum_generatorValue_eq_offset_add_labelValue,
    representationLabelValue_eq_scaledPositionalValue_labelCoefficients,
    representationLabelValue_eq_scaledPositionalValue_labelCoefficients]
  exact offset_gap_of_distinct_scaledPositionalValues
    (by simp [labelCoefficients]) hne hnorm hoffset hbudget

/-- Every exceptional sum is separated from every prescribed target. -/
theorem exceptional_gap_from_target {targets : List Int} {h M B T d : Nat}
    (hh : 2 <= h) (htarget : ∀ index, (targets.get index).natAbs <= T)
    (hbase : 2 * ((h - 1) * h) <= B) (hbudget : 2 * (h * T) + d <= M)
    {x : Int} (hx : x ∈ hFoldSumset (constructedBasis h M B targets) h)
    (hxExceptional : x ∉ prescribedTargets targets) (index : Fin targets.length) :
    d <= (x - targets.get index).natAbs := by
  obtain ⟨generators, hlength, hsum⟩ :=
    exists_generator_list_of_mem_hFoldSumset_constructedBasis hx
  have hnonzero :
      labelCoefficients h generators ≠ List.replicate targets.length 0 := by
    intro hzero
    obtain ⟨targetIndex, htargetSum⟩ :=
      exists_target_eq_sum_generatorValue_of_labelCoefficients_eq_zero
        (by omega) generators hlength hzero
    apply hxExceptional
    exact ⟨targetIndex, hsum ▸ htargetSum⟩
  have hnorm :
      l1Norm (labelCoefficients h generators) +
        l1Norm (List.replicate targets.length 0) <= B := by
    rw [l1Norm_replicate_zero, add_zero]
    have hleft := l1Norm_labelCoefficients_le hh generators
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
  rw [← hsum, sum_generatorValue_eq_offset_add_labelValue,
    representationLabelValue_eq_scaledPositionalValue_labelCoefficients]
  have hgap := offset_gap_of_distinct_scaledPositionalValues
    (xs := labelCoefficients h generators) (ys := List.replicate targets.length 0)
    (u := representationOffset generators) (v := targets.get index)
    (M := M) (B := B) (R := 2 * (h * T)) (d := d)
    (by simp [labelCoefficients]) hnonzero hnorm hoffset hbudget
  simpa [scaledPositionalValue, positionalValue_replicate_zero] using hgap

/-- Distinct exceptional sums are separated from one another. -/
theorem exceptional_gap {targets : List Int} {h M B T d : Nat}
    (hh : 2 <= h) (htarget : ∀ index, (targets.get index).natAbs <= T)
    (hbase : 2 * ((h - 1) * h) <= B) (hbudget : 2 * (h * T) + d <= M)
    {x y : Int} (hx : x ∈ hFoldSumset (constructedBasis h M B targets) h)
    (hy : y ∈ hFoldSumset (constructedBasis h M B targets) h)
    (hxExceptional : x ∉ prescribedTargets targets) (hne : x ≠ y) :
    d <= (x - y).natAbs := by
  obtain ⟨generators, hlength, hsum⟩ :=
    exists_generator_list_of_mem_hFoldSumset_constructedBasis hx
  obtain ⟨otherGenerators, hotherLength, hotherSum⟩ :=
    exists_generator_list_of_mem_hFoldSumset_constructedBasis hy
  have hnonzero :
      labelCoefficients h generators ≠ List.replicate targets.length 0 := by
    intro hzero
    obtain ⟨index, htargetSum⟩ :=
      exists_target_eq_sum_generatorValue_of_labelCoefficients_eq_zero
        (by omega) generators hlength hzero
    apply hxExceptional
    exact ⟨index, hsum ▸ htargetSum⟩
  have hcoefficients :
      labelCoefficients h generators ≠ labelCoefficients h otherGenerators := by
    intro heq
    apply hne
    rw [← hsum, ← hotherSum]
    exact sum_generatorValue_eq_of_labelCoefficients_eq_of_ne_zero
      (by omega) generators otherGenerators hlength hotherLength heq hnonzero
  rw [← hsum, ← hotherSum]
  exact gap_of_distinct_labelCoefficients hh htarget hbase hbudget
    generators otherGenerators hlength hotherLength hcoefficients

/-- Set-level form of the explicit construction: all targets occur, and all
other points are isolated from the target set and from each other. -/
theorem constructedBasis_has_isolated_exceptional_pattern
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
  refine ⟨?_, ?_, ?_⟩
  · intro index
    exact target_mem_hFoldSumset_constructedBasis targets (by omega) index
  · intro x hx hxExceptional index
    exact exceptional_gap_from_target hh htarget hbase hbudget hx hxExceptional index
  · intro x hx hxExceptional y hy hne
    exact exceptional_gap hh htarget hbase hbudget hx hy hxExceptional hne

end IntervalBases
