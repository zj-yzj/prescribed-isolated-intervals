import Formalization.SidonLabels
import Mathlib.NumberTheory.Bertrand

/-!
# Diameter and translation bounds for shifted Sidon labels

This file packages the paper-facing quantitative part of the shifted-Sidon
construction.  It keeps the elementary diameter notion explicit, proves that
translation preserves diameter, records the translation rule for double
sumsets, and uses Bertrand's postulate to choose a quadratic-size odd prime.
-/

namespace IntervalBases

/-- Every pair of elements of `basis` is at distance at most `D`. -/
def SetDiameterAtMost (basis : Set Int) (D : Nat) : Prop :=
  forall x, Membership.mem basis x ->
    forall y, Membership.mem basis y ->
      (x - y).natAbs <= D

/-- Translate an integer set by `shift`. -/
def translateIntegerSet (shift : Int) (basis : Set Int) : Set Int :=
  {x | Membership.mem basis (x - shift)}

theorem setDiameterAtMost_of_interval
    {basis : Set Int} {lower upper : Int} {D : Nat}
    (hbounds : forall x, Membership.mem basis x -> lower <= x /\ x <= upper)
    (hspan : upper - lower <= (D : Int)) :
    SetDiameterAtMost basis D := by
  intro x hx y hy
  obtain ⟨hxLower, hxUpper⟩ := hbounds x hx
  obtain ⟨hyLower, hyUpper⟩ := hbounds y hy
  rw [← Nat.cast_le (α := Int), Int.natCast_natAbs]
  apply abs_le.mpr
  constructor <;> omega

theorem setDiameterAtMost_translateIntegerSet
    {basis : Set Int} {D : Nat} (shift : Int)
    (hdiameter : SetDiameterAtMost basis D) :
    SetDiameterAtMost (translateIntegerSet shift basis) D := by
  intro x hx y hy
  have hgap := hdiameter (x - shift) hx (y - shift) hy
  simpa only [sub_sub_sub_cancel_right] using hgap

/-- Translation invariance of diameter in the reverse direction. -/
theorem setDiameterAtMost_of_translateIntegerSet
    {basis : Set Int} {D : Nat} (shift : Int)
    (hdiameter : SetDiameterAtMost (translateIntegerSet shift basis) D) :
    SetDiameterAtMost basis D := by
  intro x hx y hy
  have hgap := hdiameter (x + shift) (by
    simpa [translateIntegerSet] using hx) (y + shift) (by
      simpa [translateIntegerSet] using hy)
  simpa only [add_sub_add_right_eq_sub] using hgap

/-- Translating a basis by `shift` translates its double sumset by
`2 * shift`. -/
theorem mem_hFoldSumset_translateIntegerSet_two_iff
    {basis : Set Int} (shift x : Int) :
    Membership.mem (hFoldSumset (translateIntegerSet shift basis) 2) x ↔
      Membership.mem (hFoldSumset basis 2) (x - 2 * shift) := by
  constructor
  · rintro ⟨terms, hlength, hterms, hsum⟩
    obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp hlength
    have hleft := hterms left (by simp)
    have hright := hterms right (by simp)
    refine ⟨[left - shift, right - shift], by simp, ?_, ?_⟩
    · intro term hterm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hterm
      rcases hterm with hterm | hterm
      · subst term
        exact hleft
      · subst term
        exact hright
    · simp only [List.sum_cons, List.sum_nil, add_zero] at hsum ⊢
      rw [← hsum]
      ring
  · rintro ⟨terms, hlength, hterms, hsum⟩
    obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp hlength
    have hleft := hterms left (by simp)
    have hright := hterms right (by simp)
    refine ⟨[left + shift, right + shift], by simp, ?_, ?_⟩
    · intro term hterm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hterm
      rcases hterm with hterm | hterm
      · subst term
        simpa [translateIntegerSet] using hleft
      · subst term
        simpa [translateIntegerSet] using hright
    · simp only [List.sum_cons, List.sum_nil, add_zero] at hsum ⊢
      calc
        left + shift + (right + shift) = (left + right) + 2 * shift := by ring
        _ = (x - 2 * shift) + 2 * shift := by rw [hsum]
        _ = x := by ring

/-- Bertrand's postulate supplies an odd prime between `m` and `2 * m` when
`m >= 2`. -/
theorem exists_odd_prime_ge_lt_two_mul {m : Nat} (hm : 2 <= m) :
    Exists fun p =>
      Nat.Prime p /\ Not (p = 2) /\ m < p /\ p < 2 * m := by
  obtain ⟨p, hprime, hmLt, hpLe⟩ :=
    Nat.exists_prime_lt_and_le_two_mul m (by omega)
  refine ⟨p, hprime, ?_, hmLt, ?_⟩
  · omega
  · apply lt_of_le_of_ne hpLe
    intro heq
    have htwoDvd : 2 ∣ p := by
      rw [heq]
      exact Nat.dvd_mul_right 2 m
    rcases (Nat.dvd_prime hprime).mp htwoDvd with htwoOne | htwoP
    · omega
    · omega

/-- A bound on `natAbs` gives the corresponding signed interval bound. -/
theorem int_mem_interval_of_natAbs_le {x : Int} {T : Nat}
    (hbound : x.natAbs <= T) :
    -(T : Int) <= x /\ x <= (T : Int) := by
  have hcast : (x.natAbs : Int) <= (T : Int) := by
    exact_mod_cast hbound
  constructor
  · have hnegative := Int.le_natAbs (a := -x)
    rw [Int.natAbs_neg] at hnegative
    omega
  · exact Int.le_natAbs.trans hcast

/-- Every element of the centered shifted-Sidon basis lies in the explicit
interval used by the quadratic diameter estimate. -/
theorem shiftedSidonBasis_mem_interval
    {targets : List Int} {p M T : Nat}
    (hp : 0 < p) (hm : targets.length <= p) (hscale : T <= M)
    (htarget : forall index, (targets.get index).natAbs <= T) :
    forall x,
      Membership.mem
        (genericConstructedBasis 2 targets
          (fun index => (M : Int) * shiftedSidonLabel p index.val)) x ->
        -((4 * M * p ^ 2 : Nat) : Int) <= x /\
          x <= ((T + 4 * M * p ^ 2 : Nat) : Int) := by
  intro x hx
  rcases hx with ⟨index, hpositive | hnegative⟩
  · subst x
    obtain ⟨htargetLower, htargetUpper⟩ :=
      int_mem_interval_of_natAbs_le (htarget index)
    have hlabel :=
      shiftedSidonNatLabel_upper_bound hp (index.isLt.trans_le hm)
    have hlabelInt :
        shiftedSidonLabel p index.val < ((4 * p ^ 2 : Nat) : Int) := by
      simpa only [shiftedSidonLabel] using
        (show ((shiftedSidonNatLabel p index.val : Nat) : Int) <
            ((4 * p ^ 2 : Nat) : Int) by exact_mod_cast hlabel)
    have hlabelNonnegative : 0 <= shiftedSidonLabel p index.val := by
      simp [shiftedSidonLabel]
    have hscaledUpper :
        (M : Int) * shiftedSidonLabel p index.val <=
          ((4 * M * p ^ 2 : Nat) : Int) := by
      calc
        (M : Int) * shiftedSidonLabel p index.val <=
            (M : Int) * ((4 * p ^ 2 : Nat) : Int) :=
          mul_le_mul_of_nonneg_left hlabelInt.le (by positivity)
        _ = ((4 * M * p ^ 2 : Nat) : Int) := by push_cast; ring
    have hscaledNonnegative :
        0 <= (M : Int) * shiftedSidonLabel p index.val := by positivity
    have hlabelLowerNat := shiftedSidonNatLabel_lower_bound p index.val
    have hlabelLower :
        ((2 * p ^ 2 : Nat) : Int) <= shiftedSidonLabel p index.val := by
      simpa only [shiftedSidonLabel] using
        (show ((2 * p ^ 2 : Nat) : Int) <=
            ((shiftedSidonNatLabel p index.val : Nat) : Int) by
              exact_mod_cast hlabelLowerNat)
    have hscaleInt : (T : Int) <= (M : Int) := by exact_mod_cast hscale
    have hlabelOne : (1 : Int) <= shiftedSidonLabel p index.val := by
      have hnat : 1 <= 2 * p ^ 2 := by nlinarith
      have hcast : (1 : Int) <= ((2 * p ^ 2 : Nat) : Int) := by
        exact_mod_cast hnat
      exact hcast.trans hlabelLower
    have hscaledLower :
        (T : Int) <= (M : Int) * shiftedSidonLabel p index.val := by
      calc
        (T : Int) <= (M : Int) := hscaleInt
        _ = (M : Int) * 1 := by ring
        _ <= (M : Int) * shiftedSidonLabel p index.val :=
          mul_le_mul_of_nonneg_left hlabelOne (by positivity)
    norm_num
    constructor
    · have hnonnegative :
          0 <= targets.get index +
            (M : Int) * shiftedSidonLabel p index.val := by
        linarith
      have hleftNonpositive : -((4 * M * p ^ 2 : Nat) : Int) <= 0 :=
        neg_nonpos.mpr (by positivity)
      exact hleftNonpositive.trans hnonnegative
    · calc
        targets.get index + (M : Int) * shiftedSidonLabel p index.val <=
            (T : Int) + ((4 * M * p ^ 2 : Nat) : Int) :=
          add_le_add htargetUpper hscaledUpper
        _ = ((T + 4 * M * p ^ 2 : Nat) : Int) := by push_cast; ring
  · subst x
    have hlabel :=
      shiftedSidonNatLabel_upper_bound hp (index.isLt.trans_le hm)
    have hlabelInt :
        shiftedSidonLabel p index.val < ((4 * p ^ 2 : Nat) : Int) := by
      simpa only [shiftedSidonLabel] using
        (show ((shiftedSidonNatLabel p index.val : Nat) : Int) <
            ((4 * p ^ 2 : Nat) : Int) by exact_mod_cast hlabel)
    have hlabelNonnegative : 0 <= shiftedSidonLabel p index.val := by
      simp [shiftedSidonLabel]
    have hscaledUpper :
        (M : Int) * shiftedSidonLabel p index.val <=
          ((4 * M * p ^ 2 : Nat) : Int) := by
      calc
        (M : Int) * shiftedSidonLabel p index.val <=
            (M : Int) * ((4 * p ^ 2 : Nat) : Int) :=
          mul_le_mul_of_nonneg_left hlabelInt.le (by positivity)
        _ = ((4 * M * p ^ 2 : Nat) : Int) := by push_cast; ring
    have hscaledNonnegative :
        0 <= (M : Int) * shiftedSidonLabel p index.val := by positivity
    constructor
    · exact neg_le_neg hscaledUpper
    · have hupperNonnegative :
          0 <= ((T + 4 * M * p ^ 2 : Nat) : Int) := by positivity
      exact (neg_nonpos.mpr hscaledNonnegative).trans hupperNonnegative

/-- The centered shifted-Sidon basis has the quadratic diameter bound from the
paper. -/
theorem shiftedSidonBasis_setDiameterAtMost
    {targets : List Int} {p M T : Nat}
    (hp : 0 < p) (hm : targets.length <= p) (hscale : T <= M)
    (htarget : forall index, (targets.get index).natAbs <= T) :
    SetDiameterAtMost
      (genericConstructedBasis 2 targets
        (fun index => (M : Int) * shiftedSidonLabel p index.val))
      (T + 8 * M * p ^ 2) := by
  apply setDiameterAtMost_of_interval
    (lower := -((4 * M * p ^ 2 : Nat) : Int))
    (upper := ((T + 4 * M * p ^ 2 : Nat) : Int))
  · exact shiftedSidonBasis_mem_interval hp hm hscale htarget
  · push_cast
    ring_nf
    exact le_rfl

/-- The explicit shifted-Sidon basis already has quadratic diameter from
below: its negative generators contain the gap between the zeroth and last
labels.  Thus the quadratic order of the upper bound is sharp for this
specific construction. -/
theorem shiftedSidonBasis_diameter_lower_bound
    {targets : List Int} {p M D : Nat}
    (hlength : 1 <= targets.length) (hm : targets.length <= p)
    (hdiameter :
      SetDiameterAtMost
        (genericConstructedBasis 2 targets
          (fun index => (M : Int) * shiftedSidonLabel p index.val))
        D) :
    2 * M * targets.length * (targets.length - 1) <= D := by
  let firstIndex : Fin targets.length := ⟨0, by omega⟩
  let lastIndex : Fin targets.length := ⟨targets.length - 1, by omega⟩
  have hfirstMember :
      -((M : Int) * shiftedSidonLabel p firstIndex.val) ∈
        genericConstructedBasis 2 targets
          (fun index => (M : Int) * shiftedSidonLabel p index.val) := by
    exact ⟨firstIndex, Or.inr rfl⟩
  have hlastMember :
      -((M : Int) * shiftedSidonLabel p lastIndex.val) ∈
        genericConstructedBasis 2 targets
          (fun index => (M : Int) * shiftedSidonLabel p index.val) := by
    exact ⟨lastIndex, Or.inr rfl⟩
  have hupper :=
    hdiameter
      (-((M : Int) * shiftedSidonLabel p lastIndex.val)) hlastMember
      (-((M : Int) * shiftedSidonLabel p firstIndex.val)) hfirstMember
  have hgapNonnegative :
      shiftedSidonNatLabel p 0 <=
        shiftedSidonNatLabel p (targets.length - 1) := by
    simp [shiftedSidonNatLabel]
    omega
  have hlabelGap :
      2 * p * (targets.length - 1) <=
        (shiftedSidonLabel p (targets.length - 1) -
          shiftedSidonLabel p 0).natAbs := by
    rw [shiftedSidonLabel, shiftedSidonLabel,
      Int.natAbs_natCast_sub_natCast_of_ge]
    · exact shiftedSidonNatLabel_sub_zero_lower_bound p (targets.length - 1)
    · exact hgapNonnegative
  have hscaledGap :
      M * (2 * p * (targets.length - 1)) <=
        ((M : Int) *
          (shiftedSidonLabel p (targets.length - 1) -
            shiftedSidonLabel p 0)).natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left M hlabelGap
  have hupper' :
      ((M : Int) *
        (shiftedSidonLabel p (targets.length - 1) -
          shiftedSidonLabel p 0)).natAbs <= D := by
    calc
      ((M : Int) *
          (shiftedSidonLabel p (targets.length - 1) -
            shiftedSidonLabel p 0)).natAbs =
          (-((M : Int) *
            (shiftedSidonLabel p (targets.length - 1) -
              shiftedSidonLabel p 0))).natAbs := by
            rw [Int.natAbs_neg]
      _ =
          (-((M : Int) * shiftedSidonLabel p (targets.length - 1)) +
            (M : Int) * shiftedSidonLabel p 0).natAbs := by
              congr 1
              ring
      _ <= D := by
        simpa [firstIndex, lastIndex] using hupper
  have hlengthScaled :
      2 * M * targets.length <= 2 * M * p :=
    Nat.mul_le_mul_left (2 * M) hm
  calc
    2 * M * targets.length * (targets.length - 1) <=
        M * (2 * p * (targets.length - 1)) := by
      calc
        2 * M * targets.length * (targets.length - 1) <=
            (2 * M * p) * (targets.length - 1) :=
          Nat.mul_le_mul_right (targets.length - 1) hlengthScaled
        _ = M * (2 * p * (targets.length - 1)) := by ring
    _ <=
        ((M : Int) *
          (shiftedSidonLabel p (targets.length - 1) -
            shiftedSidonLabel p 0)).natAbs := hscaledGap
    _ <= D := hupper'

/-- The translated version of the set-level isolated-target conclusion. The
centered targets move by `2 * shift` when the basis moves by `shift`. -/
def HasTranslatedIsolatedExceptionalPatternH2
    (targets : List Int) (basis : Set Int) (shift : Int) (d : Nat) : Prop :=
  And
    (forall index : Fin targets.length,
      Membership.mem (hFoldSumset basis 2) (targets.get index + 2 * shift))
    (And
      (forall x,
        Membership.mem (hFoldSumset basis 2) x ->
          Not (Membership.mem (prescribedTargets targets) (x - 2 * shift)) ->
            forall index : Fin targets.length,
              d <= (x - (targets.get index + 2 * shift)).natAbs)
      (forall x,
        Membership.mem (hFoldSumset basis 2) x ->
          Not (Membership.mem (prescribedTargets targets) (x - 2 * shift)) ->
            forall y,
              Membership.mem (hFoldSumset basis 2) y ->
                Not (x = y) -> d <= (x - y).natAbs))

theorem hasTranslatedIsolatedExceptionalPatternH2_translateIntegerSet
    {targets : List Int} {basis : Set Int} {d : Nat} (shift : Int)
    (hpattern : HasIsolatedExceptionalPatternH2 targets basis d) :
    HasTranslatedIsolatedExceptionalPatternH2 targets
      (translateIntegerSet shift basis) shift d := by
  rw [HasIsolatedExceptionalPatternH2] at hpattern
  rw [HasTranslatedIsolatedExceptionalPatternH2]
  obtain ⟨htargets, htargetGaps, hexceptionalGaps⟩ := hpattern
  refine ⟨?_, ?_, ?_⟩
  · intro index
    rw [mem_hFoldSumset_translateIntegerSet_two_iff]
    convert htargets index using 1
    ring_nf
  · intro x hx hxExceptional index
    rw [mem_hFoldSumset_translateIntegerSet_two_iff] at hx
    have hgap := htargetGaps (x - 2 * shift) hx hxExceptional index
    convert hgap using 1
    ring_nf
  · intro x hx hxExceptional y hy hne
    rw [mem_hFoldSumset_translateIntegerSet_two_iff] at hx hy
    have hneCentered : Not (x - 2 * shift = y - 2 * shift) := by
      intro heq
      apply hne
      linarith
    have hgap :=
      hexceptionalGaps (x - 2 * shift) hx hxExceptional
        (y - 2 * shift) hy hneCentered
    convert hgap using 1
    ring_nf

/-- A translated explicit shifted-Sidon basis has the isolated-target pattern
and the same quadratic diameter bound as its centered version. -/
theorem shiftedSidonLabels_have_translated_pattern_and_diameter
    {targets : List Int} {p M T d : Nat} (shift : Int)
    (hprime : Nat.Prime p) (hodd : Not (p = 2)) (hm : targets.length <= p)
    (htarget : forall index, (targets.get index).natAbs <= T)
    (hbudget : 4 * T + d <= M) :
    And
      (HasTranslatedIsolatedExceptionalPatternH2 targets
        (translateIntegerSet shift
          (genericConstructedBasis 2 targets
            (fun index => (M : Int) * shiftedSidonLabel p index.val)))
        shift d)
      (SetDiameterAtMost
        (translateIntegerSet shift
          (genericConstructedBasis 2 targets
            (fun index => (M : Int) * shiftedSidonLabel p index.val)))
        (T + 8 * M * p ^ 2)) := by
  constructor
  · apply hasTranslatedIsolatedExceptionalPatternH2_translateIntegerSet
    exact shiftedSidonLabels_have_isolated_exceptional_pattern
      hprime hodd hm htarget hbudget
  · apply setDiameterAtMost_translateIntegerSet
    exact shiftedSidonBasis_setDiameterAtMost hprime.pos hm (by omega) htarget

/-- A diameter estimate remains valid after weakening its numerical bound. -/
theorem setDiameterAtMost_mono
    {basis : Set Int} {D E : Nat} (hdiameter : SetDiameterAtMost basis D)
    (hle : D <= E) :
    SetDiameterAtMost basis E := by
  intro x hx y hy
  exact (hdiameter x hx y hy).trans hle

/-- For at least two centered targets, Bertrand's postulate chooses an odd
prime and yields a translated shifted-Sidon basis with a diameter bound
quadratic in the number of targets alone. -/
theorem exists_shiftedSidonLabels_have_translated_pattern_and_quadratic_diameter
    {targets : List Int} {M T d : Nat} (shift : Int)
    (hlength : 2 <= targets.length)
    (htarget : forall index, (targets.get index).natAbs <= T)
    (hbudget : 4 * T + d <= M) :
    Exists fun p =>
      Nat.Prime p /\ Not (p = 2) /\
        targets.length < p /\ p < 2 * targets.length /\
          And
            (HasTranslatedIsolatedExceptionalPatternH2 targets
              (translateIntegerSet shift
                (genericConstructedBasis 2 targets
                  (fun index => (M : Int) * shiftedSidonLabel p index.val)))
              shift d)
            (SetDiameterAtMost
              (translateIntegerSet shift
                (genericConstructedBasis 2 targets
                  (fun index => (M : Int) * shiftedSidonLabel p index.val)))
              (T + 8 * M * (2 * targets.length - 1) ^ 2)) := by
  obtain ⟨p, hprime, hodd, htargetLengthLt, hpLt⟩ :=
    exists_odd_prime_ge_lt_two_mul hlength
  refine ⟨p, hprime, hodd, htargetLengthLt, hpLt, ?_⟩
  have hresult :=
    shiftedSidonLabels_have_translated_pattern_and_diameter
      shift hprime hodd htargetLengthLt.le htarget hbudget
  refine ⟨hresult.1, setDiameterAtMost_mono hresult.2 ?_⟩
  have hpSquare :
      p ^ 2 <= (2 * targets.length - 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  calc
    T + 8 * M * p ^ 2 <=
        T + 8 * M * (2 * targets.length - 1) ^ 2 := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_left (8 * M) hpSquare) T

end IntervalBases
