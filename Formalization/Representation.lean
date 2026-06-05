import Formalization.Construction

/-!
# Tagged representations and their count vectors

Every term in the explicit basis carries a sign and an index. This file
extracts the positive counts, negative counts, label coefficients, and target
offset from a tagged representation.
-/

open scoped BigOperators

namespace IntervalBases

/-- Number of positive generators carrying a fixed index. -/
def positiveCount {targets : List Int}
    (generators : List (SignedGenerator targets)) (index : Fin targets.length) : Nat :=
  generators.count (.positive index)

/-- Number of negative generators carrying a fixed index. -/
def negativeCount {targets : List Int}
    (generators : List (SignedGenerator targets)) (index : Fin targets.length) : Nat :=
  generators.count (.negative index)

/-- The coefficient of the positional label at a fixed index. -/
def labelCoefficient {targets : List Int} (h : Nat)
    (generators : List (SignedGenerator targets)) (index : Fin targets.length) : Int :=
  (h - 1) * positiveCount generators index - negativeCount generators index

/-- Coefficients ordered by the target list. -/
def labelCoefficients {targets : List Int} (h : Nat)
    (generators : List (SignedGenerator targets)) : List Int :=
  List.ofFn (labelCoefficient h generators)

/-- A positive generator contributes its target as an offset; a negative
generator has offset zero. -/
def SignedGenerator.offset {targets : List Int} :
    SignedGenerator targets -> Int
  | .positive index => targets.get index
  | .negative _ => 0

/-- Sum of the target offsets in a tagged representation. -/
def representationOffset {targets : List Int}
    (generators : List (SignedGenerator targets)) : Int :=
  (generators.map SignedGenerator.offset).sum

/-- Sum of the positional-label parts in a tagged representation. -/
def representationLabelValue {targets : List Int} (h M B : Nat)
    (generators : List (SignedGenerator targets)) : Int :=
  (generators.map fun generator =>
    generator.value h M B - generator.offset).sum

/-- Each tagged generator is counted exactly once, either positively or
negatively. -/
theorem sum_positiveCount_add_negativeCount {targets : List Int}
    (generators : List (SignedGenerator targets)) :
    (∑ index, (positiveCount generators index + negativeCount generators index)) =
      generators.length := by
  induction generators with
  | nil =>
      simp [positiveCount, negativeCount]
  | cons generator generators ih =>
      rw [Finset.sum_add_distrib] at ih
      cases generator with
      | positive generatorIndex =>
          simp only [positiveCount, negativeCount, List.count_cons]
          simp only [beq_iff_eq, SignedGenerator.positive.injEq]
          calc
            (∑ index,
                ((List.count (.positive index) generators +
                    if generatorIndex = index then 1 else 0) +
                  List.count (.negative index) generators)) =
                (∑ index,
                  (List.count (.positive index) generators +
                    List.count (.negative index) generators)) +
                  ∑ index, (if generatorIndex = index then 1 else 0) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro index _
              omega
            _ = generators.length + 1 := by
              rw [Finset.sum_add_distrib]
              change
                (∑ index, positiveCount generators index) +
                  (∑ index, negativeCount generators index) +
                  ∑ index, (if generatorIndex = index then 1 else 0) =
                    generators.length + 1
              rw [ih]
              simp
      | negative generatorIndex =>
          simp only [positiveCount, negativeCount, List.count_cons]
          simp only [beq_iff_eq, SignedGenerator.negative.injEq]
          calc
            (∑ index,
                (List.count (.positive index) generators +
                  (List.count (.negative index) generators +
                    if generatorIndex = index then 1 else 0))) =
                (∑ index,
                  (List.count (.positive index) generators +
                    List.count (.negative index) generators)) +
                  ∑ index, (if generatorIndex = index then 1 else 0) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro index _
              omega
            _ = generators.length + 1 := by
              rw [Finset.sum_add_distrib]
              change
                (∑ index, positiveCount generators index) +
                  (∑ index, negativeCount generators index) +
                  ∑ index, (if generatorIndex = index then 1 else 0) =
                    generators.length + 1
              rw [ih]
              simp

/-- The value of a representation splits into its bounded offset and its
positional-label part. -/
theorem sum_generatorValue_eq_offset_add_labelValue {targets : List Int}
    (h M B : Nat) (generators : List (SignedGenerator targets)) :
    (generators.map (SignedGenerator.value h M B)).sum =
      representationOffset generators + representationLabelValue h M B generators := by
  induction generators with
  | nil =>
      rfl
  | cons generator generators ih =>
      simp only [List.map_cons, List.sum_cons, representationOffset,
        representationLabelValue, ih]
      ring

/-- Evaluating a coefficient list created with `List.ofFn` is the usual
finite positional sum. -/
theorem positionalValue_ofFn {B n : Nat} (coefficients : Fin n -> Int) :
    positionalValue B (List.ofFn coefficients) =
      ∑ index, coefficients index * (B ^ index.val : Nat) := by
  induction n with
  | zero =>
      simp only [List.ofFn_zero, positionalValue, Finset.univ_eq_empty,
        Finset.sum_empty]
  | succ n ih =>
      rw [List.ofFn_succ, positionalValue, Fin.sum_univ_succ, ih]
      simp only [Fin.val_zero, pow_zero, Nat.cast_one, mul_one, Fin.val_succ]
      push_cast
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro index _
      rw [pow_succ]
      ring

/-- The l1 norm of a coefficient list created by `List.ofFn` is the
corresponding finite sum. -/
theorem l1Norm_ofFn {n : Nat} (coefficients : Fin n -> Int) :
    l1Norm (List.ofFn coefficients) = ∑ index, (coefficients index).natAbs := by
  induction n with
  | zero =>
      simp only [List.ofFn_zero, l1Norm, Finset.univ_eq_empty, Finset.sum_empty]
  | succ n ih =>
      rw [List.ofFn_succ, l1Norm, Fin.sum_univ_succ, ih]

/-- Counting a tagged representation and then taking a weighted coefficient
sum agrees with summing the weight contribution of each tagged generator. -/
theorem sum_labelCoefficient_mul_eq_sum_generator_weights {targets : List Int}
    (h : Nat) (generators : List (SignedGenerator targets))
    (weight : Fin targets.length -> Int) :
    (∑ index, labelCoefficient h generators index * weight index) =
      (generators.map fun generator =>
        match generator with
        | .positive index => (h - 1) * weight index
        | .negative index => -weight index).sum := by
  induction generators with
  | nil =>
      simp [labelCoefficient, positiveCount, negativeCount]
  | cons generator generators ih =>
      cases generator with
      | positive generatorIndex =>
          simp only [List.map_cons, List.sum_cons]
          rw [← ih]
          calc
            (∑ index, labelCoefficient h (.positive generatorIndex :: generators) index *
                weight index) =
                ∑ index, (((h : Int) - 1) *
                    (if generatorIndex = index then 1 else 0) * weight index +
                  labelCoefficient h generators index * weight index) := by
              apply Finset.sum_congr rfl
              intro index _
              simp only [labelCoefficient, positiveCount, negativeCount, List.count_cons,
                beq_iff_eq, SignedGenerator.positive.injEq]
              simp
              split <;> ring
            _ = (∑ index, ((h : Int) - 1) *
                  (if generatorIndex = index then 1 else 0) * weight index) +
                ∑ index, labelCoefficient h generators index * weight index := by
              rw [Finset.sum_add_distrib]
            _ = ((h : Int) - 1) * weight generatorIndex +
                ∑ index, labelCoefficient h generators index * weight index := by
              simp
      | negative generatorIndex =>
          simp only [List.map_cons, List.sum_cons]
          rw [← ih]
          calc
            (∑ index, labelCoefficient h (.negative generatorIndex :: generators) index *
                weight index) =
                ∑ index, (-(if generatorIndex = index then 1 else 0) * weight index +
                  labelCoefficient h generators index * weight index) := by
              apply Finset.sum_congr rfl
              intro index _
              simp only [labelCoefficient, positiveCount, negativeCount, List.count_cons,
                beq_iff_eq, SignedGenerator.negative.injEq]
              simp
              split <;> ring
            _ = (∑ index, -(if generatorIndex = index then 1 else 0) * weight index) +
                ∑ index, labelCoefficient h generators index * weight index := by
              rw [Finset.sum_add_distrib]
            _ = -weight generatorIndex +
                ∑ index, labelCoefficient h generators index * weight index := by
              simp

/-- The label part extracted from tagged generators is exactly the scaled
positional value of their count vector. -/
theorem representationLabelValue_eq_scaledPositionalValue_labelCoefficients
    {targets : List Int} (h M B : Nat)
    (generators : List (SignedGenerator targets)) :
    representationLabelValue h M B generators =
      scaledPositionalValue M B (labelCoefficients h generators) := by
  rw [scaledPositionalValue, labelCoefficients, positionalValue_ofFn]
  calc
    representationLabelValue h M B generators =
        ∑ index, labelCoefficient h generators index *
          positionalLabel M B index.val := by
      rw [sum_labelCoefficient_mul_eq_sum_generator_weights]
      simp only [representationLabelValue]
      apply congrArg List.sum
      apply List.map_congr_left
      intro generator _
      cases generator <;> simp [SignedGenerator.value, SignedGenerator.offset,
        positionalLabel]
    _ = M * ∑ index, labelCoefficient h generators index *
        (B ^ index.val : Nat) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      simp only [positionalLabel]
      push_cast
      ring

/-- An `h`-term tagged representation has l1 label norm at most
`(h - 1) * h`. The theorem keeps the representation length explicit so it can
also be reused before the exact `h`-term length is substituted. -/
theorem l1Norm_labelCoefficients_le {targets : List Int} {h : Nat}
    (hh : 2 <= h) (generators : List (SignedGenerator targets)) :
    l1Norm (labelCoefficients h generators) <= (h - 1) * generators.length := by
  rw [labelCoefficients, l1Norm_ofFn]
  calc
    (∑ index, (labelCoefficient h generators index).natAbs) <=
        ∑ index, ((h - 1) * positiveCount generators index +
          negativeCount generators index) := by
      apply Finset.sum_le_sum
      intro index _
      calc
        (labelCoefficient h generators index).natAbs <=
            (((h : Int) - 1) * positiveCount generators index).natAbs +
              (negativeCount generators index : Int).natAbs := by
          exact Int.natAbs_sub_le _ _
        _ = (h - 1) * positiveCount generators index +
            negativeCount generators index := by
          rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
          have hminus : ((h : Int) - 1).natAbs = h - 1 := by
            omega
          rw [hminus]
    _ = (h - 1) * (∑ index, positiveCount generators index) +
        ∑ index, negativeCount generators index := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ <= (h - 1) * ((∑ index, positiveCount generators index) +
        ∑ index, negativeCount generators index) := by
      rw [Nat.mul_add]
      exact Nat.add_le_add_left
        (Nat.le_mul_of_pos_left _ (by omega)) _
    _ = (h - 1) * generators.length := by
      congr 1
      rw [← Finset.sum_add_distrib]
      exact sum_positiveCount_add_negativeCount generators

/-- A coefficient list is the all-zero list exactly when every indexed
coefficient vanishes. -/
theorem labelCoefficients_eq_replicate_zero_iff {targets : List Int} {h : Nat}
    {generators : List (SignedGenerator targets)} :
    labelCoefficients h generators = List.replicate targets.length 0 ↔
      ∀ index, labelCoefficient h generators index = 0 := by
  rw [labelCoefficients, ← List.ofFn_const, List.ofFn_inj]
  constructor
  · intro hzero index
    exact congrFun hzero index
  · intro hzero
    exact funext hzero

/-- For `h >= 1`, an all-zero integer coefficient list gives the natural
number matching equations needed by `MatchedCounts`. -/
theorem negativeCount_eq_mul_positiveCount_of_labelCoefficients_eq_zero
    {targets : List Int} {h : Nat} (hh : 1 <= h)
    {generators : List (SignedGenerator targets)}
    (hzero : labelCoefficients h generators = List.replicate targets.length 0) :
    ∀ index, negativeCount generators index = (h - 1) * positiveCount generators index := by
  intro index
  have hcoefficient :
      labelCoefficient h generators index = 0 :=
    labelCoefficients_eq_replicate_zero_iff.mp hzero index
  simp only [labelCoefficient] at hcoefficient
  have hcast : ((h : Int) - 1) = (h - 1 : Nat) := by
    omega
  rw [hcast] at hcoefficient
  exact_mod_cast (sub_eq_zero.mp hcoefficient).symm

/-- Conversely, the natural matching equations make the integer coefficient
list vanish. -/
theorem labelCoefficients_eq_replicate_zero_of_negativeCount_eq_mul_positiveCount
    {targets : List Int} {h : Nat} (hh : 1 <= h)
    {generators : List (SignedGenerator targets)}
    (hmatched :
      ∀ index, negativeCount generators index = (h - 1) * positiveCount generators index) :
    labelCoefficients h generators = List.replicate targets.length 0 := by
  apply labelCoefficients_eq_replicate_zero_iff.mpr
  intro index
  simp only [labelCoefficient]
  have hcast : ((h : Int) - 1) = (h - 1 : Nat) := by
    omega
  rw [hcast, hmatched]
  push_cast
  ring

/-- Summing positive counts against arbitrary weights agrees with summing the
positive-generator weights directly. -/
theorem sum_positiveCount_mul_eq_sum_generator_positive_weights
    {targets : List Int} (generators : List (SignedGenerator targets))
    (weight : Fin targets.length -> Int) :
    (∑ index, (positiveCount generators index : Int) * weight index) =
      (generators.map fun generator =>
        match generator with
        | .positive index => weight index
        | .negative _ => 0).sum := by
  induction generators with
  | nil =>
      simp [positiveCount]
  | cons generator generators ih =>
      cases generator with
      | positive generatorIndex =>
          simp only [List.map_cons, List.sum_cons]
          rw [← ih]
          calc
            (∑ index, (positiveCount (.positive generatorIndex :: generators) index : Int) *
                weight index) =
                ∑ index, ((if generatorIndex = index then 1 else 0) * weight index +
                  (positiveCount generators index : Int) * weight index) := by
              apply Finset.sum_congr rfl
              intro index _
              simp only [positiveCount, List.count_cons, beq_iff_eq,
                SignedGenerator.positive.injEq]
              simp
              split <;> ring
            _ = (∑ index, (if generatorIndex = index then 1 else 0) * weight index) +
                ∑ index, (positiveCount generators index : Int) * weight index := by
              rw [Finset.sum_add_distrib]
            _ = weight generatorIndex +
                ∑ index, (positiveCount generators index : Int) * weight index := by
              simp
      | negative generatorIndex =>
          simpa [positiveCount] using ih

/-- The offset is the target-weighted sum of the positive counts. -/
theorem sum_positiveCount_mul_target_eq_representationOffset
    {targets : List Int} (generators : List (SignedGenerator targets)) :
    (∑ index, (positiveCount generators index : Int) * targets.get index) =
      representationOffset generators := by
  simpa only [representationOffset] using
    sum_positiveCount_mul_eq_sum_generator_positive_weights generators targets.get

/-- If exactly one positive generator occurs, the representation offset is
the corresponding target. -/
theorem representationOffset_eq_target_of_sum_positiveCount_eq_one
    {targets : List Int} (generators : List (SignedGenerator targets))
    (chosen : Fin targets.length) (hchosen : positiveCount generators chosen = 1)
    (hsum : (∑ index, positiveCount generators index) = 1) :
    representationOffset generators = targets.get chosen := by
  rw [← sum_positiveCount_mul_target_eq_representationOffset]
  calc
    (∑ index, (positiveCount generators index : Int) * targets.get index) =
        (positiveCount generators chosen : Int) * targets.get chosen := by
      apply Finset.sum_eq_single chosen
      · intro index _ hne
        have hsplit :
            (∑ otherIndex, positiveCount generators otherIndex) =
              positiveCount generators chosen +
                ∑ otherIndex ∈ (Finset.univ : Finset (Fin targets.length)) \ {chosen},
                  positiveCount generators otherIndex := by
          exact Finset.sum_eq_add_sum_diff_singleton_of_mem
            (f := positiveCount generators) (Finset.mem_univ chosen)
        have hrest :
            (∑ otherIndex ∈ (Finset.univ : Finset (Fin targets.length)) \ {chosen},
              positiveCount generators otherIndex) = 0 := by
          omega
        have hle : positiveCount generators index <=
            ∑ otherIndex ∈ (Finset.univ : Finset (Fin targets.length)) \ {chosen},
              positiveCount generators otherIndex :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp [hne])
        have hzero : positiveCount generators index = 0 := by
          omega
        simp only [hzero, Nat.cast_zero, zero_mul]
      · simp
    _ = targets.get chosen := by
      rw [hchosen]
      norm_num

/-- The absolute value of the offset is bounded by the representation length
times a uniform target bound. -/
theorem natAbs_representationOffset_le {targets : List Int} {T : Nat}
    (generators : List (SignedGenerator targets))
    (htarget : ∀ index, (targets.get index).natAbs <= T) :
    (representationOffset generators).natAbs <= generators.length * T := by
  induction generators with
  | nil =>
      simp [representationOffset]
  | cons generator generators ih =>
      cases generator with
      | positive index =>
          simp only [representationOffset, List.map_cons, SignedGenerator.offset,
            List.sum_cons, List.length_cons]
          calc
            (targets.get index + (generators.map SignedGenerator.offset).sum).natAbs <=
                (targets.get index).natAbs +
                  ((generators.map SignedGenerator.offset).sum).natAbs :=
              Int.natAbs_add_le _ _
            _ <= T + generators.length * T := Nat.add_le_add (htarget index) ih
            _ = (generators.length + 1) * T := by
              rw [Nat.add_mul, one_mul, Nat.add_comm]
      | negative index =>
          simp only [representationOffset, List.map_cons, SignedGenerator.offset,
            List.sum_cons, zero_add, List.length_cons]
          exact ih.trans (Nat.mul_le_mul_right T (by omega))

/-- A zero-label tagged representation is one of the prescribed target
points. -/
theorem exists_target_eq_sum_generatorValue_of_labelCoefficients_eq_zero
    {targets : List Int} {h M B : Nat} (hh : 1 <= h)
    (generators : List (SignedGenerator targets)) (hlength : generators.length = h)
    (hzero : labelCoefficients h generators = List.replicate targets.length 0) :
    ∃ index : Fin targets.length,
      (generators.map (SignedGenerator.value h M B)).sum = targets.get index := by
  have htotal :
      (∑ index, (positiveCount generators index + negativeCount generators index)) = h := by
    rw [sum_positiveCount_add_negativeCount, hlength]
  have hmatched :
      ∀ index, negativeCount generators index = (h - 1) * positiveCount generators index :=
    negativeCount_eq_mul_positiveCount_of_labelCoefficients_eq_zero hh hzero
  obtain ⟨index, hpositive, _⟩ :=
    exists_matched_index hh (positiveCount generators) (negativeCount generators)
      htotal hmatched
  have hpositiveSum : (∑ index, positiveCount generators index) = 1 :=
    sum_positive_counts_eq_one hh (positiveCount generators) (negativeCount generators)
      htotal hmatched
  refine ⟨index, ?_⟩
  rw [sum_generatorValue_eq_offset_add_labelValue,
    representationOffset_eq_target_of_sum_positiveCount_eq_one generators index
      hpositive hpositiveSum,
    representationLabelValue_eq_scaledPositionalValue_labelCoefficients, hzero,
    scaledPositionalValue, positionalValue_replicate_zero, mul_zero, add_zero]

end IntervalBases
