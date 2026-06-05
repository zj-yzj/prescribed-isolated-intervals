import Formalization.PaperCorollary

/-!
# Exact cardinality of the explicit basis

The integer-valued basis is the range of the tagged generators. Under the
paper's parameter bounds, distinct tagged generators have distinct values:
negative generators are negative, positive generators are positive, and
same-sign generators are separated by positional labels.
-/

namespace IntervalBases

/-- Distinct positional labels differ by at least the scale `M`. -/
theorem positionalLabel_gap {M B r s : Nat} (hB : 2 <= B)
    (hne : r ≠ s) :
    M <= (positionalLabel M B r - positionalLabel M B s).natAbs := by
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · change M <= (((M * B ^ r : Nat) : Int) - (M * B ^ s : Nat)).natAbs
    rw [Int.natAbs_natCast_sub_natCast_of_le]
    · have hpow : B ^ r < B ^ s := pow_right_strictMono₀ (by omega) hrs
      have hdiff : 1 <= B ^ s - B ^ r := by omega
      calc
        M = M * 1 := by omega
        _ <= M * (B ^ s - B ^ r) := Nat.mul_le_mul_left M hdiff
        _ = M * B ^ s - M * B ^ r := Nat.mul_sub_left_distrib M _ _
    · exact Nat.mul_le_mul_left M
        ((pow_right_strictMono₀ (by omega : 1 < B)).monotone hrs.le)
  · change M <= (((M * B ^ r : Nat) : Int) - (M * B ^ s : Nat)).natAbs
    rw [Int.natAbs_natCast_sub_natCast_of_ge]
    · have hpow : B ^ s < B ^ r := pow_right_strictMono₀ (by omega) hsr
      have hdiff : 1 <= B ^ r - B ^ s := by omega
      calc
        M = M * 1 := by omega
        _ <= M * (B ^ r - B ^ s) := Nat.mul_le_mul_left M hdiff
        _ = M * B ^ r - M * B ^ s := Nat.mul_sub_left_distrib M _ _
    · exact Nat.mul_le_mul_left M
        ((pow_right_strictMono₀ (by omega : 1 < B)).monotone hsr.le)

/-- Multiplying labels by the positive factor `h - 1` preserves a gap of at
least `M`. -/
theorem scaled_positionalLabel_gap {h M B r s : Nat} (hh : 2 <= h)
    (hB : 2 <= B) (hne : r ≠ s) :
    M <= (((h : Int) - 1) * positionalLabel M B r -
      ((h : Int) - 1) * positionalLabel M B s).natAbs := by
  rw [← mul_sub, Int.natAbs_mul]
  calc
    M <= (positionalLabel M B r - positionalLabel M B s).natAbs :=
      positionalLabel_gap hB hne
    _ <= (((h : Int) - 1).natAbs) *
        (positionalLabel M B r - positionalLabel M B s).natAbs := by
      exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr (by omega))

/-- Two target offsets differ by at most `2T`. -/
theorem target_sub_target_natAbs_le {targets : List Int} {T : Nat}
    (htarget : ∀ index, (targets.get index).natAbs <= T)
    (left right : Fin targets.length) :
    (targets.get left - targets.get right).natAbs <= 2 * T := by
  calc
    (targets.get left - targets.get right).natAbs <=
        (targets.get left).natAbs + (targets.get right).natAbs :=
      Int.natAbs_sub_le _ _
    _ <= T + T := Nat.add_le_add (htarget left) (htarget right)
    _ = 2 * T := by omega

/-- Positive generators are separated from one another. -/
theorem positiveGeneratorValue_gap {targets : List Int} {h M B T : Nat}
    (hh : 2 <= h) (hM : 2 * T + 1 <= M) (hB : 2 <= B)
    (htarget : ∀ index, (targets.get index).natAbs <= T)
    {left right : Fin targets.length} (hne : left ≠ right) :
    1 <= ((SignedGenerator.positive left).value h M B -
      (SignedGenerator.positive right).value h M B).natAbs := by
  apply offset_gap
  · exact scaled_positionalLabel_gap hh hB
      (fun heq => hne (Fin.ext heq))
  · exact target_sub_target_natAbs_le htarget left right
  · exact hM

/-- Every positional label is positive. -/
theorem positionalLabel_pos {M B r : Nat} (hM : 1 <= M) (hB : 1 <= B) :
    0 < positionalLabel M B r := by
  simp only [positionalLabel]
  positivity

/-- A target bounded by `T` is bounded below by `-T`. -/
theorem neg_target_bound {targets : List Int} {T : Nat}
    (htarget : ∀ index, (targets.get index).natAbs <= T)
    (index : Fin targets.length) :
    -(T : Int) <= targets.get index := by
  have hlower := Int.le_natAbs (a := -(targets.get index))
  rw [Int.natAbs_neg] at hlower
  have hbound := htarget index
  omega

/-- Every positive tagged generator has a positive integer value. -/
theorem positiveGeneratorValue_pos {targets : List Int} {h M B T : Nat}
    (hh : 2 <= h) (hM : T + 1 <= M) (hB : 1 <= B)
    (htarget : ∀ index, (targets.get index).natAbs <= T)
    (index : Fin targets.length) :
    0 < (SignedGenerator.positive index).value h M B := by
  simp only [SignedGenerator.value]
  have hlabel : (M : Int) <= positionalLabel M B index.val := by
    simp only [positionalLabel]
    have hpow : 1 <= B ^ index.val := one_le_pow₀ hB
    nlinarith
  have hlower := neg_target_bound htarget index
  have hfactor : (1 : Int) <= (h : Int) - 1 := by omega
  nlinarith

/-- Every negative tagged generator has a negative integer value. -/
theorem negativeGeneratorValue_neg {targets : List Int} {M B : Nat}
    (hM : 1 <= M) (hB : 1 <= B) (index : Fin targets.length) :
    (SignedGenerator.negative index).value 0 M B < 0 := by
  simp only [SignedGenerator.value]
  exact neg_neg_of_pos (positionalLabel_pos hM hB)

/-- The tagged-generator value map is injective. -/
theorem signedGeneratorValue_injective {targets : List Int} {h M B T : Nat}
    (hh : 2 <= h) (hM : 2 * T + 1 <= M) (hB : 2 <= B)
    (htarget : ∀ index, (targets.get index).natAbs <= T) :
    Function.Injective (SignedGenerator.value (targets := targets) h M B) := by
  intro left right heq
  cases left with
  | positive leftIndex =>
      cases right with
      | positive rightIndex =>
          congr 1
          by_contra hne
          have hgap :=
            positiveGeneratorValue_gap hh hM hB htarget
              hne
          rw [heq, sub_self, Int.natAbs_zero] at hgap
          omega
      | negative rightIndex =>
          have hpositive := positiveGeneratorValue_pos (targets := targets)
            (h := h) (M := M) (T := T) (B := B)
            hh (by omega) (by omega) htarget leftIndex
          have hnegative := negativeGeneratorValue_neg (targets := targets) (M := M) (B := B)
            (by omega) (by omega) rightIndex
          simp only [SignedGenerator.value] at heq hpositive hnegative
          omega
  | negative leftIndex =>
      cases right with
      | positive rightIndex =>
          have hnegative := negativeGeneratorValue_neg (targets := targets) (M := M) (B := B)
            (by omega) (by omega) leftIndex
          have hpositive := positiveGeneratorValue_pos (targets := targets)
            (h := h) (M := M) (T := T) (B := B)
            hh (by omega) (by omega) htarget rightIndex
          simp only [SignedGenerator.value] at heq hpositive hnegative
          omega
      | negative rightIndex =>
          congr 1
          by_contra hne
          have hgap := positionalLabel_gap (M := M) (B := B) hB
            (fun heq => hne (Fin.ext heq))
          simp only [SignedGenerator.value] at heq
          have hlabelEq : positionalLabel M B leftIndex.val =
              positionalLabel M B rightIndex.val := by omega
          rw [hlabelEq, sub_self, Int.natAbs_zero] at hgap
          omega

/-- Tagged generators are equivalent to two copies of the target indices. -/
def signedGeneratorEquiv (targets : List Int) :
    SignedGenerator targets ≃ Fin targets.length ⊕ Fin targets.length where
  toFun
    | .positive index => Sum.inl index
    | .negative index => Sum.inr index
  invFun
    | .inl index => .positive index
    | .inr index => .negative index
  left_inv generator := by cases generator <;> rfl
  right_inv index := by cases index <;> rfl

/-- There are exactly two tagged generators per target point. -/
theorem natCard_signedGenerator (targets : List Int) :
    Nat.card (SignedGenerator targets) = 2 * targets.length := by
  rw [Nat.card_congr (signedGeneratorEquiv targets), Nat.card_sum,
    Nat.card_fin]
  omega

/-- The integer-valued basis is the range of the tagged-generator value map. -/
theorem constructedBasis_eq_range_generatorValue {targets : List Int} {h M B : Nat} :
    constructedBasis h M B targets =
      Set.range (SignedGenerator.value (targets := targets) h M B) := by
  ext x
  rw [mem_constructedBasis_iff_exists_generator]
  rfl

/-- Exact cardinality of the explicit basis. -/
theorem ncard_constructedBasis {targets : List Int} {h M B T : Nat}
    (hh : 2 <= h) (hM : 2 * T + 1 <= M) (hB : 2 <= B)
    (htarget : ∀ index, (targets.get index).natAbs <= T) :
    (constructedBasis h M B targets).ncard = 2 * targets.length := by
  rw [constructedBasis_eq_range_generatorValue,
    Set.ncard_range_of_injective (signedGeneratorValue_injective hh hM hB htarget),
    natCard_signedGenerator]

/-- Exact basis cardinality after flattening a family of intervals. -/
theorem ncard_constructedBasis_intervalTargets
    {starts : List Int} {n h M B T : Nat}
    (hh : 2 <= h) (hM : 2 * T + 1 <= M) (hB : 2 <= B)
    (htarget : ∀ index : Fin (intervalTargets starts n).length,
      ((intervalTargets starts n).get index).natAbs <= T) :
    (constructedBasis h M B (intervalTargets starts n)).ncard =
      2 * (starts.length * (n + 1)) := by
  rw [ncard_constructedBasis hh hM hB htarget, length_intervalTargets]

/-- Paper-facing theorem: the explicit basis has the requested maximal
nontrivial intervals and exact cardinality `2 q (n + 1)`. -/
theorem prescribedIsolatedIntervals
    {starts : List Int} {n h M B T d : Nat}
    (hsep : SeparatedStarts starts n) (hn : 1 <= n) (hh : 2 <= h) (hd : 2 <= d)
    (htarget : ∀ index : Fin (intervalTargets starts n).length,
      ((intervalTargets starts n).get index).natAbs <= T)
    (hbase : 2 * ((h - 1) * h) <= B) (hbudget : 2 * (h * T) + d <= M) :
    HasExactlyNontrivialIntervals
      (hFoldSumset (constructedBasis h M B (intervalTargets starts n)) h) starts n ∧
    (∀ lower upper : Int,
      IsMaximalNontrivialInterval
        (hFoldSumset (constructedBasis h M B (intervalTargets starts n)) h) lower upper ↔
        ∃ start ∈ starts, lower = start ∧ upper = start + n) ∧
    (constructedBasis h M B (intervalTargets starts n)).ncard =
      2 * (starts.length * (n + 1)) := by
  have hBcard : 2 <= B := by
    have hfactor : 0 < (h - 1) * h :=
      Nat.mul_pos (by omega) (by omega)
    omega
  have hMcard : 2 * T + 1 <= M := by
    have hT : T <= h * T := Nat.le_mul_of_pos_left T (by omega)
    omega
  refine ⟨constructedBasis_has_exactly_nontrivial_intervals
    hsep hh hd htarget hbase hbudget, ?_, ?_⟩
  · intro lower upper
    exact constructedBasis_isMaximalNontrivialInterval_iff
      hsep hn hh hd htarget hbase hbudget
  · exact ncard_constructedBasis_intervalTargets hh hMcard hBcard htarget

/-- The scale used in the paper. -/
def paperScale (h T d : Nat) : Nat :=
  2 * (h * T) + d

/-- The positional base used in the paper, written in the order convenient
for the formal separation budget. It equals `2 * h * (h - 1)`. -/
def paperBase (h : Nat) : Nat :=
  2 * ((h - 1) * h)

/-- Fully instantiated paper theorem with the explicit scale and base. -/
theorem explicitPrescribedIsolatedIntervals
    {starts : List Int} {n h T d : Nat}
    (hsep : SeparatedStarts starts n) (hn : 1 <= n) (hh : 2 <= h) (hd : 2 <= d)
    (htarget : ∀ index : Fin (intervalTargets starts n).length,
      ((intervalTargets starts n).get index).natAbs <= T) :
    HasExactlyNontrivialIntervals
      (hFoldSumset
        (constructedBasis h (paperScale h T d) (paperBase h) (intervalTargets starts n)) h)
      starts n ∧
    (∀ lower upper : Int,
      IsMaximalNontrivialInterval
        (hFoldSumset
          (constructedBasis h (paperScale h T d) (paperBase h) (intervalTargets starts n)) h)
        lower upper ↔
        ∃ start ∈ starts, lower = start ∧ upper = start + n) ∧
    (constructedBasis h (paperScale h T d) (paperBase h)
      (intervalTargets starts n)).ncard =
        2 * (starts.length * (n + 1)) := by
  apply prescribedIsolatedIntervals hsep hn hh hd htarget
  · rfl
  · rfl

/-- Closed paper theorem: choose the radius directly from the flattened
target list, then use the explicit scale and base. -/
theorem explicitPrescribedIsolatedIntervalsWithRadius
    {starts : List Int} {n h d : Nat}
    (hsep : SeparatedStarts starts n) (hn : 1 <= n) (hh : 2 <= h) (hd : 2 <= d) :
    HasExactlyNontrivialIntervals
      (hFoldSumset
        (constructedBasis h (paperScale h (intervalTargetRadius starts n) d) (paperBase h)
          (intervalTargets starts n)) h)
      starts n ∧
    (∀ lower upper : Int,
      IsMaximalNontrivialInterval
        (hFoldSumset
          (constructedBasis h (paperScale h (intervalTargetRadius starts n) d) (paperBase h)
            (intervalTargets starts n)) h)
        lower upper ↔
        ∃ start ∈ starts, lower = start ∧ upper = start + n) ∧
    (constructedBasis h (paperScale h (intervalTargetRadius starts n) d) (paperBase h)
      (intervalTargets starts n)).ncard =
        2 * (starts.length * (n + 1)) := by
  apply explicitPrescribedIsolatedIntervals hsep hn hh hd
  intro index
  exact natAbs_get_le_targetRadius index

end IntervalBases
