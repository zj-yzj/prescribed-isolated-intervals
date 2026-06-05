import Formalization.GenericLabelInstances
import Formalization.Centering

/-!
# Closed diameter bounds for finite moment labels

This file packages the paper-facing quantitative part of the finite-moment
construction. It proves an explicit largest-label bound, derives the centered
diameter estimate, translates the basis back to the original targets, and
selects all numerical parameters automatically once a translation is given.
-/

namespace IntervalBases

/-- Natural-valued version of the finite moment label. -/
def momentNatLabel (L Q r : Nat) : Nat :=
  Finset.univ.sum fun j : Fin L => r ^ j.val * Q ^ j.val

/-- Uniform upper bound for the moment labels on an `m`-point target list. -/
def momentLabelRadiusSum (m L Q : Nat) : Nat :=
  Finset.univ.sum fun j : Fin L =>
    labelRadius m ^ j.val * Q ^ j.val

/-- The integer-valued moment label is the coercion of its natural-valued
counterpart. -/
theorem momentLabel_eq_natCast (L Q r : Nat) :
    momentLabel L Q r = (momentNatLabel L Q r : Int) := by
  rw [momentLabel, momentNatLabel]
  push_cast
  rfl

/-- Moment labels are bounded by the uniform radius sum on the relevant
index range. -/
theorem momentNatLabel_le_radiusSum
    {m L Q : Nat} (index : Fin m) :
    momentNatLabel L Q index.val <= momentLabelRadiusSum m L Q := by
  rw [momentNatLabel, momentLabelRadiusSum]
  apply Finset.sum_le_sum
  intro j _
  exact Nat.mul_le_mul_right (Q ^ j.val) <|
    Nat.pow_le_pow_left (fin_val_le_labelRadius index) j.val

/-- A moment label contains the constant term `1`. -/
theorem one_le_momentNatLabel {L Q r : Nat} (hL : 1 <= L) :
    1 <= momentNatLabel L Q r := by
  let zeroIndex : Fin L := ⟨0, hL⟩
  calc
    1 = r ^ zeroIndex.val * Q ^ zeroIndex.val := by simp [zeroIndex]
    _ <= Finset.univ.sum (fun j : Fin L => r ^ j.val * Q ^ j.val) := by
      exact Finset.single_le_sum
        (f := fun j : Fin L => r ^ j.val * Q ^ j.val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ zeroIndex)
    _ = momentNatLabel L Q r := by rfl

/-- Every scaled moment label is bounded by the scaled radius sum. -/
theorem scaledMomentLabel_le_radiusSum
    {m M L Q : Nat} (index : Fin m) :
    scaledMomentLabel M L Q index.val <=
      ((M * momentLabelRadiusSum m L Q : Nat) : Int) := by
  rw [scaledMomentLabel, momentLabel_eq_natCast]
  exact_mod_cast Nat.mul_le_mul_left M (momentNatLabel_le_radiusSum index)

/-- Every scaled moment label is nonnegative. -/
theorem scaledMomentLabel_nonnegative (M L Q r : Nat) :
    0 <= scaledMomentLabel M L Q r := by
  rw [scaledMomentLabel, momentLabel_eq_natCast]
  positivity

/-- A scaled moment label is at least its scale when `L >= 1`. -/
theorem scale_le_scaledMomentLabel {M L Q r : Nat} (hL : 1 <= L) :
    (M : Int) <= scaledMomentLabel M L Q r := by
  rw [scaledMomentLabel, momentLabel_eq_natCast]
  have hbound : M <= M * momentNatLabel L Q r := by
    simpa using Nat.mul_le_mul_left M (one_le_momentNatLabel hL)
  exact_mod_cast hbound

/-- Every element of the centered moment-label basis lies in the interval
used by the paper's closed diameter estimate. -/
theorem momentConstructedBasis_mem_interval
    {targets : List Int} {h M L Q T : Nat}
    (hh : 2 <= h) (hL : 1 <= L) (hscale : T <= M)
    (htarget : forall index, (targets.get index).natAbs <= T) :
    forall x,
      Membership.mem (momentConstructedBasis h M L Q targets) x ->
        -((M * momentLabelRadiusSum targets.length L Q : Nat) : Int) <= x /\
          x <=
            ((T + (h - 1) * M *
              momentLabelRadiusSum targets.length L Q : Nat) : Int) := by
  intro x hx
  rcases hx with ⟨index, hpositive | hnegative⟩
  · subst x
    obtain ⟨htargetLower, htargetUpper⟩ :=
      int_mem_interval_of_natAbs_le (htarget index)
    have hlabelUpper := scaledMomentLabel_le_radiusSum (M := M) (L := L) (Q := Q) index
    have hlabelLower := scale_le_scaledMomentLabel (M := M) (Q := Q) (r := index.val) hL
    have hscaleInt : (T : Int) <= (M : Int) := by exact_mod_cast hscale
    have hfactor : (1 : Int) <= (h : Int) - 1 := by omega
    have hnonnegative :
        0 <= targets.get index +
          ((h : Int) - 1) * scaledMomentLabel M L Q index.val := by
      nlinarith
    constructor
    · exact
        (neg_nonpos.mpr (by positivity)).trans hnonnegative
    · calc
        targets.get index +
              ((h : Int) - 1) * scaledMomentLabel M L Q index.val <=
            (T : Int) + ((h : Int) - 1) *
              ((M * momentLabelRadiusSum targets.length L Q : Nat) : Int) := by
          exact add_le_add htargetUpper <|
            mul_le_mul_of_nonneg_left hlabelUpper (by omega)
        _ =
            ((T + (h - 1) * M *
              momentLabelRadiusSum targets.length L Q : Nat) : Int) := by
          push_cast
          have hcastSub : (((h - 1 : Nat) : Int)) = (h : Int) - 1 := by omega
          rw [hcastSub]
          ring
  · subst x
    have hlabelUpper := scaledMomentLabel_le_radiusSum (M := M) (L := L) (Q := Q) index
    have hlabelNonnegative := scaledMomentLabel_nonnegative M L Q index.val
    constructor
    · exact neg_le_neg hlabelUpper
    · exact
        (neg_nonpos.mpr hlabelNonnegative).trans (by positivity)

/-- The centered moment-label basis has the paper's explicit diameter bound. -/
theorem momentConstructedBasis_setDiameterAtMost
    {targets : List Int} {h M L Q T : Nat}
    (hh : 2 <= h) (hL : 1 <= L) (hscale : T <= M)
    (htarget : forall index, (targets.get index).natAbs <= T) :
    SetDiameterAtMost
      (momentConstructedBasis h M L Q targets)
      (T + h * M * momentLabelRadiusSum targets.length L Q) := by
  apply setDiameterAtMost_of_interval
    (lower := -((M * momentLabelRadiusSum targets.length L Q : Nat) : Int))
    (upper := ((T + (h - 1) * M *
      momentLabelRadiusSum targets.length L Q : Nat) : Int))
  · exact momentConstructedBasis_mem_interval hh hL hscale htarget
  · have hcastSub : (((h - 1 : Nat) : Int)) = (h : Int) - 1 := by omega
    push_cast
    rw [hcastSub]
    ring_nf
    exact le_rfl

/-- The moment-label set-level theorem in the reusable isolated-pattern
interface. -/
theorem momentConstructedBasis_has_pattern
    {targets : List Int} {h M L Q T d : Nat}
    (hh : 2 <= h) (htarget : forall index, (targets.get index).natAbs <= T)
    (horder : 2 * ((h - 1) * h) <= L)
    (hbase : momentEncodingBase targets.length L <= Q)
    (hbudget : 2 * (h * T) + d <= M) :
    HasIsolatedExceptionalPattern targets
      (momentConstructedBasis h M L Q targets) h d := by
  rw [HasIsolatedExceptionalPattern]
  exact momentConstructedBasis_has_isolated_exceptional_pattern
    hh htarget horder hbase hbudget

/-- The translated moment-label basis attached to an original target list. -/
def translatedMomentBasis (targets : List Int) (h : Nat) (shift : Int)
    (M L Q : Nat) : Set Int :=
  translateIntegerSet shift
    (momentConstructedBasis h M L Q (centerTargets h shift targets))

/-- A translated explicit moment-label basis realizes the original target
list, retains the diameter estimate, and has exact cardinality `2m`. -/
theorem translatedMomentBasis_has_pattern_diameter_cardinality
    {targets : List Int} {h M L Q T d : Nat} (shift : Int)
    (hh : 2 <= h)
    (htarget : forall index : Fin (centerTargets h shift targets).length,
      ((centerTargets h shift targets).get index).natAbs <= T)
    (horder : 2 * ((h - 1) * h) <= L)
    (hbase : momentEncodingBase targets.length L <= Q)
    (hbudget : 2 * (h * T) + d <= M) (hd : 1 <= d) :
    And
      (HasIsolatedExceptionalPattern targets
        (translatedMomentBasis targets h shift M L Q) h d)
      (And
        (SetDiameterAtMost
          (translatedMomentBasis targets h shift M L Q)
          (T + h * M * momentLabelRadiusSum targets.length L Q))
        ((translatedMomentBasis targets h shift M L Q).ncard =
          2 * targets.length)) := by
  have hcenteredBase :
      momentEncodingBase (centerTargets h shift targets).length L <= Q := by
    simpa using hbase
  have hcenteredOrder :
      BoundedLabelSeparation
        (fun index : Fin (centerTargets h shift targets).length =>
          scaledMomentLabel M L Q index.val)
        (2 * ((h - 1) * h)) M :=
    scaledMomentLabel_boundedLabelSeparation horder hcenteredBase
  have hT : T <= h * T := Nat.le_mul_of_pos_left T (by omega)
  have hscale : T <= M := by omega
  have hcardBudget : 2 * T + 1 <= M := by omega
  have hL : 1 <= L := by
    have hpositive : 0 < (h - 1) * h :=
      Nat.mul_pos (by omega) (by omega)
    omega
  refine ⟨?_, ?_, ?_⟩
  · apply hasIsolatedExceptionalPattern_translateIntegerSet shift
    exact momentConstructedBasis_has_pattern
      hh htarget horder hcenteredBase hbudget
  · apply setDiameterAtMost_translateIntegerSet
    simpa using
      (momentConstructedBasis_setDiameterAtMost
        hh hL hscale htarget)
  · rw [translatedMomentBasis, ncard_translateIntegerSet_general]
    simpa [genericConstructedBasis, momentConstructedBasis] using
      (ncard_genericConstructedBasis
        hh htarget hcenteredOrder hcardBudget)

/-- Relation order used by the paper's finite-moment construction. -/
def paperMomentOrder (h : Nat) : Nat :=
  2 * ((h - 1) * h)

/-- Radius after centering an arbitrary target list for an `h`-fold
translation. -/
def centeredTargetRadius (targets : List Int) (h : Nat) (shift : Int) : Nat :=
  targetRadius (centerTargets h shift targets)

/-- Scale used by the closed finite-moment construction. -/
def paperMomentScale (targets : List Int) (h : Nat) (shift : Int) (d : Nat) : Nat :=
  2 * (h * centeredTargetRadius targets h shift) + d

/-- Encoding base used by the closed finite-moment construction. -/
def paperMomentEncodingBase (targets : List Int) (h : Nat) : Nat :=
  momentEncodingBase targets.length (paperMomentOrder h)

/-- Fully instantiated translated finite-moment basis. -/
def explicitTranslatedMomentBasis (targets : List Int) (h : Nat)
    (shift : Int) (d : Nat) : Set Int :=
  translatedMomentBasis targets h shift
    (paperMomentScale targets h shift d)
    (paperMomentOrder h)
    (paperMomentEncodingBase targets h)

/-- Closed finite-list theorem: after a translation is supplied, Lean
selects the target radius, relation order, scale, and encoding base
automatically. -/
theorem explicitTranslatedMomentBasis_has_pattern_diameter_cardinality
    {targets : List Int} {h d : Nat} (shift : Int)
    (hh : 2 <= h) (hd : 1 <= d) :
    And
      (HasIsolatedExceptionalPattern targets
        (explicitTranslatedMomentBasis targets h shift d) h d)
      (And
        (SetDiameterAtMost
          (explicitTranslatedMomentBasis targets h shift d)
          (centeredTargetRadius targets h shift +
            h * paperMomentScale targets h shift d *
              momentLabelRadiusSum targets.length
                (paperMomentOrder h) (paperMomentEncodingBase targets h)))
        ((explicitTranslatedMomentBasis targets h shift d).ncard =
          2 * targets.length)) := by
  have htarget :
      forall index : Fin (centerTargets h shift targets).length,
        ((centerTargets h shift targets).get index).natAbs <=
          centeredTargetRadius targets h shift := by
    intro index
    exact natAbs_get_le_targetRadius index
  apply translatedMomentBasis_has_pattern_diameter_cardinality
    (M := paperMomentScale targets h shift d)
    (L := paperMomentOrder h)
    (Q := paperMomentEncodingBase targets h)
    (T := centeredTargetRadius targets h shift)
    shift hh htarget
  · rfl
  · simp [paperMomentEncodingBase]
  · rfl
  · exact hd

/-- Position-independent radius bound obtained by centering targets inside
an enclosing interval. -/
def enclosedTargetRadiusBound (lower upper : Int) (h : Nat) : Nat :=
  natHalfCeil ((upper - lower).natAbs + h)

/-- Position-independent diameter bound for the fully instantiated
finite-moment basis. -/
def enclosedMomentDiameterBound (targets : List Int) (h d : Nat)
    (lower upper : Int) : Nat :=
  let T := enclosedTargetRadiusBound lower upper h
  T + h * (2 * (h * T) + d) *
    momentLabelRadiusSum targets.length
      (paperMomentOrder h) (paperMomentEncodingBase targets h)

/-- Closed finite-list theorem with automatic centering: if the prescribed
targets lie in an enclosing interval, Lean selects a translation and proves
the position-independent diameter bound. -/
theorem exists_explicitTranslatedMomentBasis_has_pattern_diameter_cardinality_enclosed
    {targets : List Int} {h d : Nat}
    (hh : 2 <= h) (hd : 1 <= d) (lower upper : Int)
    (hbounds : forall target, target ∈ targets ->
      lower <= target /\ target <= upper) :
    Exists fun shift : Int =>
      And
        (HasIsolatedExceptionalPattern targets
          (explicitTranslatedMomentBasis targets h shift d) h d)
        (And
          (SetDiameterAtMost
            (explicitTranslatedMomentBasis targets h shift d)
            (enclosedMomentDiameterBound targets h d lower upper))
          ((explicitTranslatedMomentBasis targets h shift d).ncard =
            2 * targets.length)) := by
  obtain ⟨shift, hcenteredRadius⟩ :=
    exists_shift_targetRadius_centerTargets_le_natHalfCeil
      targets h (by omega) lower upper hbounds
  have hresult :=
    explicitTranslatedMomentBasis_has_pattern_diameter_cardinality
      (targets := targets) (d := d) shift hh hd
  refine ⟨shift, hresult.1, ?_, hresult.2.2⟩
  apply setDiameterAtMost_mono hresult.2.1
  rw [enclosedMomentDiameterBound, enclosedTargetRadiusBound,
    paperMomentScale]
  apply Nat.add_le_add hcenteredRadius
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_left h
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left h hcenteredRadius)) d

/-- Closed interval-family corollary for the finite-moment construction. -/
theorem explicitTranslatedMomentBasis_has_exactly_intervals
    {starts : List Int} {n h d : Nat} (shift : Int)
    (hsep : SeparatedStarts starts n) (hn : 1 <= n)
    (hh : 2 <= h) (hd : 2 <= d) :
    And
      (HasExactlyNontrivialIntervals
        (hFoldSumset
          (explicitTranslatedMomentBasis (intervalTargets starts n) h shift d) h)
        starts n)
      (And
        (forall lower upper : Int,
          IsMaximalNontrivialInterval
            (hFoldSumset
              (explicitTranslatedMomentBasis
                (intervalTargets starts n) h shift d) h)
            lower upper <->
              Exists fun start =>
                Membership.mem starts start /\
                  lower = start /\ upper = start + n)
        (And
          (SetDiameterAtMost
            (explicitTranslatedMomentBasis (intervalTargets starts n) h shift d)
            (centeredTargetRadius (intervalTargets starts n) h shift +
              h * paperMomentScale (intervalTargets starts n) h shift d *
                momentLabelRadiusSum (intervalTargets starts n).length
                  (paperMomentOrder h)
                  (paperMomentEncodingBase (intervalTargets starts n) h)))
          ((explicitTranslatedMomentBasis
            (intervalTargets starts n) h shift d).ncard =
              2 * (intervalTargets starts n).length))) := by
  have hresult :=
    explicitTranslatedMomentBasis_has_pattern_diameter_cardinality
      (targets := intervalTargets starts n) (d := d) shift hh (by omega)
  refine ⟨?_, ?_, hresult.2.1, hresult.2.2⟩
  · exact
      hasIsolatedExceptionalPattern_hasExactlyNontrivialIntervals
        hsep hd hresult.1
  · intro lower upper
    exact isMaximalNontrivialInterval_iff hsep hn
      (hasIsolatedExceptionalPattern_hasExactlyNontrivialIntervals
        hsep hd hresult.1)

/-- Closed interval-family corollary with an automatically selected
centering shift and a position-independent diameter bound. -/
theorem exists_explicitTranslatedMomentBasis_has_exactly_intervals_enclosed
    {starts : List Int} {n h d : Nat}
    (lower upper : Int)
    (hbounds : forall target, target ∈ intervalTargets starts n ->
      lower <= target /\ target <= upper)
    (hsep : SeparatedStarts starts n) (hn : 1 <= n)
    (hh : 2 <= h) (hd : 2 <= d) :
    Exists fun shift : Int =>
      And
        (HasExactlyNontrivialIntervals
          (hFoldSumset
            (explicitTranslatedMomentBasis
              (intervalTargets starts n) h shift d) h)
          starts n)
        (And
          (forall intervalLower intervalUpper : Int,
            IsMaximalNontrivialInterval
              (hFoldSumset
                (explicitTranslatedMomentBasis
                  (intervalTargets starts n) h shift d) h)
              intervalLower intervalUpper <->
                Exists fun start =>
                  Membership.mem starts start /\
                    intervalLower = start /\ intervalUpper = start + n)
          (And
            (SetDiameterAtMost
              (explicitTranslatedMomentBasis
                (intervalTargets starts n) h shift d)
              (enclosedMomentDiameterBound
                (intervalTargets starts n) h d lower upper))
            ((explicitTranslatedMomentBasis
              (intervalTargets starts n) h shift d).ncard =
                2 * (intervalTargets starts n).length))) := by
  obtain ⟨shift, hresult⟩ :=
    exists_explicitTranslatedMomentBasis_has_pattern_diameter_cardinality_enclosed
      (targets := intervalTargets starts n) (d := d)
      hh (by omega) lower upper hbounds
  refine ⟨shift, ?_, ?_, hresult.2.1, hresult.2.2⟩
  · exact
      hasIsolatedExceptionalPattern_hasExactlyNontrivialIntervals
        hsep hd hresult.1
  · intro intervalLower intervalUpper
    exact isMaximalNontrivialInterval_iff hsep hn
      (hasIsolatedExceptionalPattern_hasExactlyNontrivialIntervals
        hsep hd hresult.1)

end IntervalBases
