import Mathlib

/-!
# Positional separation for prescribed isolated intervals

This file formalizes the arithmetic separation lemma used in
`research/draft.tex`. The combinatorial construction is developed on top of
this lemma.
-/

namespace IntervalBases

/-- The geometric tail below `B ^ R` is strictly smaller than `B ^ R` when
`B ≥ 2`. -/
theorem geom_tail_lt_top {B R : ℕ} (hB : 2 ≤ B) :
    ∑ r ∈ Finset.range R, B ^ r < B ^ R := by
  induction R with
  | zero =>
      simp
  | succ R ih =>
      rw [Finset.sum_range_succ, pow_succ]
      calc
        ∑ r ∈ Finset.range R, B ^ r + B ^ R
            < B ^ R + B ^ R := Nat.add_lt_add_right ih _
        _ = 2 * B ^ R := by omega
        _ ≤ B * B ^ R := Nat.mul_le_mul_right _ hB
        _ = B ^ R * B := Nat.mul_comm _ _


/-- The sum of the absolute values of a list of integer coefficients. -/
def l1Norm : List Int -> Nat
  | [] => 0
  | z :: zs => z.natAbs + l1Norm zs

/-- Evaluate a coefficient list in base `B`, with the lowest coefficient
first. -/
def positionalValue (B : Nat) : List Int -> Int
  | [] => 0
  | z :: zs => z + B * positionalValue B zs

@[simp]
theorem l1Norm_replicate_zero (n : Nat) : l1Norm (List.replicate n 0) = 0 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simpa only [List.replicate_succ, l1Norm, Int.natAbs_zero, zero_add] using ih

@[simp]
theorem positionalValue_replicate_zero (B n : Nat) :
    positionalValue B (List.replicate n 0) = 0 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change (0 : Int) + B * positionalValue B (List.replicate n 0) = 0
      simp only [ih, mul_zero, add_zero]

theorem l1Norm_pos_of_ne_replicate_zero {coefficients : List Int}
    (hne : Not (coefficients = List.replicate coefficients.length 0)) :
    1 <= l1Norm coefficients := by
  induction coefficients with
  | nil =>
      simp at hne
  | cons z zs ih =>
      simp only [l1Norm]
      by_cases hz : z = 0
      · subst z
        simp only [Int.natAbs_zero, zero_add]
        apply ih
        intro hzs
        apply hne
        rw [List.length_cons, List.replicate_succ]
        exact congrArg (List.cons (0 : Int)) hzs
      · have hzPos : 1 <= z.natAbs := Int.natAbs_pos.mpr hz
        omega

/-- A bounded, nonzero signed coefficient list cannot evaluate to zero in a
base at least as large as its l1 norm. -/
theorem positionalValue_ne_zero_of_l1Norm_le_base {B : Nat}
    {coefficients : List Int} (hnorm : l1Norm coefficients <= B)
    (hne : Not (coefficients = List.replicate coefficients.length 0)) :
    Not (positionalValue B coefficients = 0) := by
  induction coefficients with
  | nil =>
      simp at hne
  | cons z zs ih =>
      simp only [positionalValue]
      by_cases hzs : zs = List.replicate zs.length 0
      · have hz : Not (z = 0) := by
          intro hz
          subst z
          apply hne
          rw [List.length_cons, List.replicate_succ]
          exact congrArg (List.cons (0 : Int)) hzs
        rw [hzs, positionalValue_replicate_zero, mul_zero, add_zero]
        exact hz
      · have htailNorm : l1Norm zs <= B := by
          simp only [l1Norm] at hnorm
          omega
        have htailValue : Not (positionalValue B zs = 0) := ih htailNorm hzs
        intro hvalue
        have hEq : (B : Int) * positionalValue B zs = -z := by
          omega
        have hAbsEq : B * (positionalValue B zs).natAbs = z.natAbs := by
          have := congrArg Int.natAbs hEq
          simpa only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_neg] using this
        have htailAbsPos : 1 <= (positionalValue B zs).natAbs :=
          Int.natAbs_pos.mpr htailValue
        have htailNormPos : 1 <= l1Norm zs :=
          l1Norm_pos_of_ne_replicate_zero hzs
        simp only [l1Norm] at hnorm
        nlinarith

/-- After scaling the positional labels by `M`, every nonzero bounded
coefficient combination has absolute value at least `M`. -/
theorem scale_le_natAbs_mul_positionalValue {M B : Nat}
    {coefficients : List Int} (hnorm : l1Norm coefficients <= B)
    (hne : Not (coefficients = List.replicate coefficients.length 0)) :
    M <= ((M : Int) * positionalValue B coefficients).natAbs := by
  rw [Int.natAbs_mul]
  simp only [Int.natAbs_natCast]
  exact Nat.le_mul_of_pos_right M <|
    Int.natAbs_pos.mpr (positionalValue_ne_zero_of_l1Norm_le_base hnorm hne)

/-- Pointwise subtraction for two coefficient lists. -/
def coefficientDifference : List Int -> List Int -> List Int
  | x :: xs, y :: ys => (x - y) :: coefficientDifference xs ys
  | _, _ => []

theorem length_coefficientDifference {xs ys : List Int}
    (hlen : xs.length = ys.length) :
    (coefficientDifference xs ys).length = xs.length := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          rfl
      | cons y ys =>
          simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at hlen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [coefficientDifference, List.length_cons, ih hlen]

theorem l1Norm_coefficientDifference_le {xs ys : List Int}
    (hlen : xs.length = ys.length) :
    l1Norm (coefficientDifference xs ys) <= l1Norm xs + l1Norm ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          rfl
      | cons y ys =>
          simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at hlen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [coefficientDifference, l1Norm]
          calc
            (x - y).natAbs + l1Norm (coefficientDifference xs ys)
                <= (x.natAbs + y.natAbs) + (l1Norm xs + l1Norm ys) :=
              Nat.add_le_add (Int.natAbs_sub_le x y) (ih hlen)
            _ = (x.natAbs + l1Norm xs) + (y.natAbs + l1Norm ys) := by omega

theorem coefficientDifference_ne_replicate_zero {xs ys : List Int}
    (hlen : xs.length = ys.length) (hne : Not (xs = ys)) :
    Not (coefficientDifference xs ys = List.replicate xs.length 0) := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          exact (hne rfl).elim
      | cons y ys =>
          simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at hlen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rw [coefficientDifference, List.length_cons, List.replicate_succ,
            List.cons.injEq]
          intro hdiff
          rcases hdiff with ⟨hhead, htail⟩
          apply hne
          have hxy : x = y := sub_eq_zero.mp hhead
          have hxsys : xs = ys := by
            by_contra hneTail
            exact ih hlen hneTail htail
          simp only [hxy, hxsys]

theorem positionalValue_coefficientDifference {B : Nat} {xs ys : List Int}
    (hlen : xs.length = ys.length) :
    positionalValue B (coefficientDifference xs ys) =
      positionalValue B xs - positionalValue B ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          rfl
      | cons y ys =>
          simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at hlen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [coefficientDifference, positionalValue, ih hlen]
          ring

/-- The scaled value represented by a coefficient vector and positional
labels `M * B ^ r`. -/
def scaledPositionalValue (M B : Nat) (coefficients : List Int) : Int :=
  M * positionalValue B coefficients

/-- Paper-facing form of positional separation: two distinct bounded label
vectors have scaled values at least `M` apart. -/
theorem scale_le_natAbs_sub_scaledPositionalValue {M B : Nat}
    {xs ys : List Int} (hlen : xs.length = ys.length) (hne : Not (xs = ys))
    (hnorm : l1Norm xs + l1Norm ys <= B) :
    M <= (scaledPositionalValue M B xs - scaledPositionalValue M B ys).natAbs := by
  rw [scaledPositionalValue, scaledPositionalValue, ← mul_sub,
    ← positionalValue_coefficientDifference hlen]
  apply scale_le_natAbs_mul_positionalValue
  · exact (l1Norm_coefficientDifference_le hlen).trans hnorm
  · simpa only [length_coefficientDifference hlen] using
      coefficientDifference_ne_replicate_zero hlen hne

end IntervalBases
