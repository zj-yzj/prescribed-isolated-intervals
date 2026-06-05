import Formalization.TranslatedPatterns

/-!
# Centering a finite target list

This file packages the elementary rounding argument used to make the
diameter bounds independent of the absolute position of the prescribed
targets.  A multiple of `h` can be chosen within `h / 2` of the midpoint of
an enclosing interval.  The integer-valued formulation below avoids
fractions: the doubled error is at most `h`.
-/

namespace IntervalBases

/-- Natural-valued ceiling of division by two. -/
def natHalfCeil (n : Nat) : Nat :=
  (n + 1) / 2

/-- Every integer is within `h` of an even multiple of `h`.  Applied to the
sum of two endpoints, this is the nearest-multiple form of midpoint
rounding. -/
theorem exists_shift_sub_two_mul_natAbs_le (h : Nat) (hh : 1 <= h) (z : Int) :
    Exists fun shift : Int =>
      (z - 2 * (h : Int) * shift).natAbs <= h := by
  let modulus : Int := 2 * (h : Int)
  let quotient : Int := z / modulus
  let remainder : Int := z % modulus
  have hmodulusPositive : 0 < modulus := by
    dsimp [modulus]
    omega
  have hremainderNonnegative : 0 <= remainder := by
    exact Int.emod_nonneg z (ne_of_gt hmodulusPositive)
  have hremainderLt : remainder < modulus := by
    exact Int.emod_lt_of_pos z hmodulusPositive
  have hdecomposition : remainder + modulus * quotient = z := by
    exact Int.emod_add_mul_ediv z modulus
  by_cases hsmall : remainder <= (h : Int)
  · refine ⟨quotient, ?_⟩
    have heq : z - 2 * (h : Int) * quotient = remainder := by
      dsimp [modulus] at hdecomposition
      linarith
    rw [heq, ← Nat.cast_le (α := Int), Int.natCast_natAbs,
      abs_of_nonneg hremainderNonnegative]
    exact hsmall
  · refine ⟨quotient + 1, ?_⟩
    have heq :
        z - 2 * (h : Int) * (quotient + 1) =
          -(modulus - remainder) := by
      dsimp [modulus] at hdecomposition ⊢
      linarith
    have hgapNonnegative : 0 <= modulus - remainder := by
      omega
    rw [heq, Int.natAbs_neg, ← Nat.cast_le (α := Int),
      Int.natCast_natAbs, abs_of_nonneg hgapNonnegative]
    have hgapBound : modulus - remainder <= (h : Int) := by
      dsimp [modulus] at *
      omega
    exact_mod_cast hgapBound

/-- If the doubled midpoint error of `shift` is at most `h`, every point of
an enclosing interval is at distance at most
`ceil ((diameter + h) / 2)` from `h * shift`. -/
theorem sub_mul_shift_natAbs_le_natHalfCeil
    {lower upper x shift : Int} {h : Nat}
    (hlower : lower <= x) (hupper : x <= upper)
    (hshift :
      (lower + upper - 2 * (h : Int) * shift).natAbs <= h) :
    (x - (h : Int) * shift).natAbs <=
      natHalfCeil ((upper - lower).natAbs + h) := by
  have hdiameterNonnegative : 0 <= upper - lower := by
    omega
  have hshiftBounds :=
    int_mem_interval_of_natAbs_le hshift
  have hdoubleBounds :
      -((((upper - lower).natAbs + h : Nat) : Int)) <=
          2 * (x - (h : Int) * shift) /\
        2 * (x - (h : Int) * shift) <=
          (((upper - lower).natAbs + h : Nat) : Int) := by
    push_cast
    rw [abs_of_nonneg hdiameterNonnegative]
    ring_nf at hshiftBounds ⊢
    constructor <;> omega
  have hdoubleNatAbs :
      (2 * (x - (h : Int) * shift)).natAbs <=
        (upper - lower).natAbs + h := by
    rw [← Nat.cast_le (α := Int), Int.natCast_natAbs]
    exact abs_le.mpr hdoubleBounds
  rw [Int.natAbs_mul] at hdoubleNatAbs
  norm_num at hdoubleNatAbs
  rw [natHalfCeil]
  omega

/-- A uniform bound for every list member bounds `targetRadius`. -/
theorem targetRadius_le_of_forall_mem
    {targets : List Int} {T : Nat}
    (hbound : forall target, target ∈ targets -> target.natAbs <= T) :
    targetRadius targets <= T := by
  induction targets with
  | nil =>
      simp [targetRadius]
  | cons target targets ih =>
      simp only [targetRadius, max_le_iff]
      constructor
      · exact hbound target (by simp)
      · apply ih
        intro member hmember
        exact hbound member (by simp [hmember])

/-- A finite target list contained in an interval admits an `h`-fold
centering shift with a position-independent radius bound. -/
theorem exists_shift_targetRadius_centerTargets_le_natHalfCeil
    (targets : List Int) (h : Nat) (hh : 1 <= h)
    (lower upper : Int)
    (hbounds : forall target, target ∈ targets ->
      lower <= target /\ target <= upper) :
    Exists fun shift : Int =>
      targetRadius (centerTargets h shift targets) <=
        natHalfCeil ((upper - lower).natAbs + h) := by
  obtain ⟨shift, hshift⟩ :=
    exists_shift_sub_two_mul_natAbs_le h hh (lower + upper)
  refine ⟨shift, ?_⟩
  apply targetRadius_le_of_forall_mem
  intro centeredTarget hcenteredTarget
  rw [centerTargets] at hcenteredTarget
  obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hcenteredTarget
  obtain ⟨hlower, hupper⟩ := hbounds target htarget
  exact sub_mul_shift_natAbs_le_natHalfCeil hlower hupper hshift

end IntervalBases
