import Formalization.SetLevelPackaging
import Formalization.MomentSeparation

/-!
# Abstract separated label families

The combinatorial part of the isolated-target construction does not depend on
the formula for the labels. It only needs bounded coefficient vectors to have
well-separated label values. This file packages that reusable interface and
proves the set-level construction once for an arbitrary separated label
family.
-/

namespace IntervalBases

/-- Evaluation of an indexed coefficient function against an arbitrary label
family. -/
def linearLabelValue {m : Nat} (labels coefficients : Fin m -> Int) : Int :=
  Finset.univ.sum fun index => coefficients index * labels index

/-- An abstract label family separates all distinct coefficient functions
whose combined l1 norm is at most `L`. -/
def BoundedLabelSeparation {m : Nat} (labels : Fin m -> Int) (L M : Nat) : Prop :=
  forall {xs ys : Fin m -> Int},
    Not (xs = ys) ->
      functionL1Norm xs + functionL1Norm ys <= L ->
        M <= (linearLabelValue labels xs - linearLabelValue labels ys).natAbs

/-- A tagged generator evaluated using an arbitrary label family. -/
def SignedGenerator.genericValue {targets : List Int} (h : Nat)
    (labels : Fin targets.length -> Int) :
    SignedGenerator targets -> Int
  | .positive index => targets.get index + (h - 1) * labels index
  | .negative index => -labels index

/-- The signed basis associated with an arbitrary label family. -/
def genericConstructedBasis (h : Nat) (targets : List Int)
    (labels : Fin targets.length -> Int) : Set Int :=
  {x | Exists fun index : Fin targets.length =>
    x = targets.get index + (h - 1) * labels index \/
      x = -labels index}

theorem mem_genericConstructedBasis_iff_exists_generator {h : Nat}
    {targets : List Int} {labels : Fin targets.length -> Int} {x : Int} :
    x ∈ genericConstructedBasis h targets labels ↔
      Exists fun generator : SignedGenerator targets =>
        generator.genericValue h labels = x := by
  constructor
  · rintro ⟨index, hpositive | hnegative⟩
    · exact ⟨.positive index, hpositive.symm⟩
    · exact ⟨.negative index, hnegative.symm⟩
  · rintro ⟨generator, rfl⟩
    cases generator with
    | positive index =>
        exact ⟨index, Or.inl rfl⟩
    | negative index =>
        exact ⟨index, Or.inr rfl⟩

theorem exists_generic_generator_list_of_terms {h : Nat}
    {targets : List Int} {labels : Fin targets.length -> Int}
    (terms : List Int)
    (hterms : ∀ term ∈ terms, term ∈ genericConstructedBasis h targets labels) :
    Exists fun generators : List (SignedGenerator targets) =>
      generators.map (SignedGenerator.genericValue h labels) = terms := by
  induction terms with
  | nil =>
      exact ⟨[], rfl⟩
  | cons term terms ih =>
      obtain ⟨generator, hgenerator⟩ :=
        mem_genericConstructedBasis_iff_exists_generator.mp (hterms term (by simp))
      obtain ⟨generators, hgenerators⟩ := ih (by
        intro tailTerm htailTerm
        exact hterms tailTerm (by simp only [List.mem_cons, htailTerm, or_true]))
      refine ⟨generator :: generators, ?_⟩
      simp only [List.map_cons, hgenerator, hgenerators]

theorem exists_generic_generator_list_of_mem_hFoldSumset {h : Nat}
    {targets : List Int} {labels : Fin targets.length -> Int} {x : Int}
    (hx : x ∈ hFoldSumset (genericConstructedBasis h targets labels) h) :
    Exists fun generators : List (SignedGenerator targets) =>
      generators.length = h /\
        (generators.map (SignedGenerator.genericValue h labels)).sum = x := by
  obtain ⟨terms, hlength, hterms, hsum⟩ := hx
  obtain ⟨generators, hgenerators⟩ :=
    exists_generic_generator_list_of_terms terms hterms
  refine ⟨generators, ?_, ?_⟩
  · rw [← List.length_map (f := SignedGenerator.genericValue h labels), hgenerators]
    exact hlength
  · rw [hgenerators]
    exact hsum

/-- Every target has its matched representation for any label family. -/
theorem target_mem_hFoldSumset_genericConstructedBasis {h : Nat}
    (targets : List Int) (labels : Fin targets.length -> Int)
    (hh : 1 <= h) (index : Fin targets.length) :
    targets.get index ∈ hFoldSumset (genericConstructedBasis h targets labels) h := by
  let a := labels index
  refine ⟨(targets.get index + (h - 1) * a) :: List.replicate (h - 1) (-a), ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_replicate]
    omega
  · intro term hterm
    simp only [List.mem_cons, List.mem_replicate] at hterm
    rcases hterm with hterm | hterm
    · subst term
      exact ⟨index, Or.inl rfl⟩
    · rcases hterm with ⟨_, hterm⟩
      subst term
      exact ⟨index, Or.inr rfl⟩
  · simp only [List.sum_cons, List.sum_replicate]
    dsimp only [a]
    have hsplit : h = (h - 1) + 1 := by omega
    rw [hsplit]
    push_cast
    ring

/-- Sum of the label parts in a generic tagged representation. -/
def genericRepresentationLabelValue {targets : List Int} (h : Nat)
    (labels : Fin targets.length -> Int)
    (generators : List (SignedGenerator targets)) : Int :=
  (generators.map fun generator =>
    generator.genericValue h labels - generator.offset).sum

theorem sum_genericGeneratorValue_eq_offset_add_labelValue {targets : List Int}
    (h : Nat) (labels : Fin targets.length -> Int)
    (generators : List (SignedGenerator targets)) :
    (generators.map (SignedGenerator.genericValue h labels)).sum =
      representationOffset generators +
        genericRepresentationLabelValue h labels generators := by
  induction generators with
  | nil =>
      rfl
  | cons generator generators ih =>
      simp only [List.map_cons, List.sum_cons, representationOffset,
        genericRepresentationLabelValue, ih]
      ring

theorem genericRepresentationLabelValue_eq_linearLabelValue
    {targets : List Int} (h : Nat) (labels : Fin targets.length -> Int)
    (generators : List (SignedGenerator targets)) :
    genericRepresentationLabelValue h labels generators =
      linearLabelValue labels (labelCoefficient h generators) := by
  calc
    genericRepresentationLabelValue h labels generators =
        Finset.univ.sum fun index =>
          labelCoefficient h generators index * labels index := by
      rw [sum_labelCoefficient_mul_eq_sum_generator_weights]
      simp only [genericRepresentationLabelValue]
      apply congrArg List.sum
      apply List.map_congr_left
      intro generator _
      cases generator <;> simp [SignedGenerator.genericValue, SignedGenerator.offset]
    _ = linearLabelValue labels (labelCoefficient h generators) := rfl

theorem functionL1Norm_labelCoefficient_le_generic {targets : List Int} {h : Nat}
    (hh : 2 <= h) (generators : List (SignedGenerator targets)) :
    functionL1Norm (labelCoefficient h generators) <=
      (h - 1) * generators.length := by
  rw [functionL1Norm, ← l1Norm_ofFn]
  exact l1Norm_labelCoefficients_le hh generators

theorem labelCoefficients_eq_of_labelCoefficient_eq_generic
    {targets : List Int} {h : Nat}
    {generators otherGenerators : List (SignedGenerator targets)}
    (hcoefficients :
      labelCoefficient h generators = labelCoefficient h otherGenerators) :
    labelCoefficients h generators = labelCoefficients h otherGenerators := by
  simp only [labelCoefficients, hcoefficients]

theorem labelCoefficients_eq_replicate_zero_of_labelCoefficient_eq_zero_generic
    {targets : List Int} {h : Nat} {generators : List (SignedGenerator targets)}
    (hzero : labelCoefficient h generators = 0) :
    labelCoefficients h generators = List.replicate targets.length 0 := by
  apply labelCoefficients_eq_replicate_zero_iff.mpr
  intro index
  exact congrFun hzero index

/-- A zero-label generic representation is one of the prescribed targets. -/
theorem exists_target_eq_sum_genericGeneratorValue_of_labelCoefficient_eq_zero
    {targets : List Int} {h : Nat} (labels : Fin targets.length -> Int)
    (hh : 1 <= h) (generators : List (SignedGenerator targets))
    (hlength : generators.length = h)
    (hzero : labelCoefficient h generators = 0) :
    Exists fun index : Fin targets.length =>
      (generators.map (SignedGenerator.genericValue h labels)).sum =
        targets.get index := by
  have hzeroList :
      labelCoefficients h generators = List.replicate targets.length 0 :=
    labelCoefficients_eq_replicate_zero_of_labelCoefficient_eq_zero_generic hzero
  have htotal :
      (Finset.univ.sum fun index =>
        positiveCount generators index + negativeCount generators index) = h := by
    rw [sum_positiveCount_add_negativeCount, hlength]
  have hmatched :
      ∀ index, negativeCount generators index =
        (h - 1) * positiveCount generators index :=
    negativeCount_eq_mul_positiveCount_of_labelCoefficients_eq_zero hh hzeroList
  obtain ⟨index, hpositive, _⟩ :=
    exists_matched_index hh (positiveCount generators) (negativeCount generators)
      htotal hmatched
  have hpositiveSum :
      (Finset.univ.sum fun index => positiveCount generators index) = 1 :=
    sum_positive_counts_eq_one hh (positiveCount generators) (negativeCount generators)
      htotal hmatched
  refine ⟨index, ?_⟩
  rw [sum_genericGeneratorValue_eq_offset_add_labelValue,
    representationOffset_eq_target_of_sum_positiveCount_eq_one generators index
      hpositive hpositiveSum,
    genericRepresentationLabelValue_eq_linearLabelValue, hzero]
  simp [linearLabelValue]

/-- Equal nonzero count coefficient functions determine the same exceptional
sum for any label family. -/
theorem sum_genericGeneratorValue_eq_of_labelCoefficient_eq_of_ne_zero
    {targets : List Int} {h : Nat} (labels : Fin targets.length -> Int)
    (hh : 1 <= h)
    (generators otherGenerators : List (SignedGenerator targets))
    (hlength : generators.length = h) (hotherLength : otherGenerators.length = h)
    (hcoefficients :
      labelCoefficient h generators = labelCoefficient h otherGenerators)
    (hnonzero : Not (labelCoefficient h generators = 0)) :
    (generators.map (SignedGenerator.genericValue h labels)).sum =
      (otherGenerators.map (SignedGenerator.genericValue h labels)).sum := by
  have hcoefficientLists :
      labelCoefficients h generators = labelCoefficients h otherGenerators :=
    labelCoefficients_eq_of_labelCoefficient_eq_generic hcoefficients
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
      genericRepresentationLabelValue h labels generators =
        genericRepresentationLabelValue h labels otherGenerators := by
    rw [genericRepresentationLabelValue_eq_linearLabelValue,
      genericRepresentationLabelValue_eq_linearLabelValue, hcoefficients]
  rw [sum_genericGeneratorValue_eq_offset_add_labelValue,
    sum_genericGeneratorValue_eq_offset_add_labelValue, hoffset, hlabel]

theorem genericGap_of_distinct_labelCoefficients
    {targets : List Int} {h M T d : Nat} {labels : Fin targets.length -> Int}
    (hh : 2 <= h) (htarget : ∀ index, (targets.get index).natAbs <= T)
    (hseparate : BoundedLabelSeparation labels (2 * ((h - 1) * h)) M)
    (hbudget : 2 * (h * T) + d <= M)
    (generators otherGenerators : List (SignedGenerator targets))
    (hlength : generators.length = h) (hotherLength : otherGenerators.length = h)
    (hne : Not (labelCoefficient h generators =
      labelCoefficient h otherGenerators)) :
    d <= ((generators.map (SignedGenerator.genericValue h labels)).sum -
      (otherGenerators.map (SignedGenerator.genericValue h labels)).sum).natAbs := by
  have hnorm :
      functionL1Norm (labelCoefficient h generators) +
        functionL1Norm (labelCoefficient h otherGenerators) <= 2 * ((h - 1) * h) := by
    have hleft := functionL1Norm_labelCoefficient_le_generic hh generators
    have hright := functionL1Norm_labelCoefficient_le_generic hh otherGenerators
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
  rw [sum_genericGeneratorValue_eq_offset_add_labelValue,
    sum_genericGeneratorValue_eq_offset_add_labelValue,
    genericRepresentationLabelValue_eq_linearLabelValue,
    genericRepresentationLabelValue_eq_linearLabelValue]
  exact offset_gap (hseparate hne hnorm) hoffset hbudget

theorem genericExceptional_gap_from_target
    {targets : List Int} {h M T d : Nat} {labels : Fin targets.length -> Int}
    (hh : 2 <= h) (htarget : ∀ index, (targets.get index).natAbs <= T)
    (hseparate : BoundedLabelSeparation labels (2 * ((h - 1) * h)) M)
    (hbudget : 2 * (h * T) + d <= M)
    {x : Int} (hx : x ∈ hFoldSumset (genericConstructedBasis h targets labels) h)
    (hxExceptional : x ∉ prescribedTargets targets) (index : Fin targets.length) :
    d <= (x - targets.get index).natAbs := by
  obtain ⟨generators, hlength, hsum⟩ :=
    exists_generic_generator_list_of_mem_hFoldSumset hx
  have hnonzero : Not (labelCoefficient h generators = 0) := by
    intro hzero
    obtain ⟨targetIndex, htargetSum⟩ :=
      exists_target_eq_sum_genericGeneratorValue_of_labelCoefficient_eq_zero
        labels (by omega) generators hlength hzero
    apply hxExceptional
    exact ⟨targetIndex, hsum ▸ htargetSum⟩
  have hzeroNorm : functionL1Norm (0 : Fin targets.length -> Int) = 0 := by
    simp [functionL1Norm]
  have hnorm :
      functionL1Norm (labelCoefficient h generators) +
        functionL1Norm (0 : Fin targets.length -> Int) <= 2 * ((h - 1) * h) := by
    rw [hzeroNorm, add_zero]
    have hleft := functionL1Norm_labelCoefficient_le_generic hh generators
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
  rw [← hsum, sum_genericGeneratorValue_eq_offset_add_labelValue,
    genericRepresentationLabelValue_eq_linearLabelValue]
  have hgap := offset_gap
    (hseparate hnonzero hnorm) hoffset hbudget
  simpa [linearLabelValue] using hgap

theorem genericExceptional_gap
    {targets : List Int} {h M T d : Nat} {labels : Fin targets.length -> Int}
    (hh : 2 <= h) (htarget : ∀ index, (targets.get index).natAbs <= T)
    (hseparate : BoundedLabelSeparation labels (2 * ((h - 1) * h)) M)
    (hbudget : 2 * (h * T) + d <= M)
    {x y : Int} (hx : x ∈ hFoldSumset (genericConstructedBasis h targets labels) h)
    (hy : y ∈ hFoldSumset (genericConstructedBasis h targets labels) h)
    (hxExceptional : x ∉ prescribedTargets targets) (hne : x ≠ y) :
    d <= (x - y).natAbs := by
  obtain ⟨generators, hlength, hsum⟩ :=
    exists_generic_generator_list_of_mem_hFoldSumset hx
  obtain ⟨otherGenerators, hotherLength, hotherSum⟩ :=
    exists_generic_generator_list_of_mem_hFoldSumset hy
  have hnonzero : Not (labelCoefficient h generators = 0) := by
    intro hzero
    obtain ⟨index, htargetSum⟩ :=
      exists_target_eq_sum_genericGeneratorValue_of_labelCoefficient_eq_zero
        labels (by omega) generators hlength hzero
    apply hxExceptional
    exact ⟨index, hsum ▸ htargetSum⟩
  have hcoefficients :
      Not (labelCoefficient h generators = labelCoefficient h otherGenerators) := by
    intro heq
    apply hne
    rw [← hsum, ← hotherSum]
    exact sum_genericGeneratorValue_eq_of_labelCoefficient_eq_of_ne_zero
      labels (by omega) generators otherGenerators hlength hotherLength heq hnonzero
  rw [← hsum, ← hotherSum]
  exact genericGap_of_distinct_labelCoefficients hh htarget hseparate hbudget
    generators otherGenerators hlength hotherLength hcoefficients

/-- Abstract set-level isolation theorem. Power labels and moment labels are
instances of this statement. -/
theorem genericConstructedBasis_has_isolated_exceptional_pattern
    {targets : List Int} {h M T d : Nat} {labels : Fin targets.length -> Int}
    (hh : 2 <= h) (htarget : ∀ index, (targets.get index).natAbs <= T)
    (hseparate : BoundedLabelSeparation labels (2 * ((h - 1) * h)) M)
    (hbudget : 2 * (h * T) + d <= M) :
    (∀ index : Fin targets.length,
      targets.get index ∈ hFoldSumset (genericConstructedBasis h targets labels) h) ∧
    (∀ x ∈ hFoldSumset (genericConstructedBasis h targets labels) h,
      x ∉ prescribedTargets targets ->
        ∀ index : Fin targets.length, d <= (x - targets.get index).natAbs) ∧
    (∀ x ∈ hFoldSumset (genericConstructedBasis h targets labels) h,
      x ∉ prescribedTargets targets ->
        ∀ y ∈ hFoldSumset (genericConstructedBasis h targets labels) h,
          x ≠ y -> d <= (x - y).natAbs) := by
  refine ⟨?_, ?_, ?_⟩
  · intro index
    exact target_mem_hFoldSumset_genericConstructedBasis targets labels (by omega) index
  · intro x hx hxExceptional index
    exact genericExceptional_gap_from_target hh htarget hseparate hbudget
      hx hxExceptional index
  · intro x hx hxExceptional y hy hne
    exact genericExceptional_gap hh htarget hseparate hbudget
      hx hy hxExceptional hne

end IntervalBases
