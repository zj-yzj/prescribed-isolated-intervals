import Formalization.GenericCardinality
import Formalization.SidonDiameter

/-!
# Translation of general h-fold sumsets and isolated patterns

The shifted-Sidon layer only needs the case `h = 2`. Moment labels work for
all `h >= 2`, so this file packages the general translation rule.
-/

namespace IntervalBases

/-- Subtracting a fixed integer from every list term subtracts
`terms.length * shift` from the list sum. -/
theorem sum_map_sub_const (terms : List Int) (shift : Int) :
    (terms.map fun term => term - shift).sum =
      terms.sum - (terms.length : Int) * shift := by
  induction terms with
  | nil =>
      simp
  | cons term terms ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      push_cast
      ring

/-- Adding a fixed integer to every list term adds
`terms.length * shift` to the list sum. -/
theorem sum_map_add_const (terms : List Int) (shift : Int) :
    (terms.map fun term => term + shift).sum =
      terms.sum + (terms.length : Int) * shift := by
  induction terms with
  | nil =>
      simp
  | cons term terms ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      push_cast
      ring

/-- Translating a basis by `shift` translates its `h`-fold sumset by
`h * shift`. -/
theorem mem_hFoldSumset_translateIntegerSet_iff
    {basis : Set Int} (h : Nat) (shift x : Int) :
    Membership.mem (hFoldSumset (translateIntegerSet shift basis) h) x <->
      Membership.mem (hFoldSumset basis h) (x - (h : Int) * shift) := by
  constructor
  · rintro ⟨terms, hlength, hterms, hsum⟩
    refine ⟨terms.map (fun term => term - shift), by simpa, ?_, ?_⟩
    · intro term hterm
      obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
      exact hterms source hsource
    · rw [sum_map_sub_const, hsum, hlength]
  · rintro ⟨terms, hlength, hterms, hsum⟩
    refine ⟨terms.map (fun term => term + shift), by simpa, ?_, ?_⟩
    · intro term hterm
      obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
      simpa [translateIntegerSet] using hterms source hsource
    · rw [sum_map_add_const, hsum, hlength]
      ring

/-- Translation preserves the exact cardinality of an integer set. -/
theorem ncard_translateIntegerSet_general (shift : Int) (basis : Set Int) :
    (translateIntegerSet shift basis).ncard = basis.ncard := by
  have hset :
      translateIntegerSet shift basis = (fun x : Int => x + shift) '' basis := by
    ext x
    constructor
    · intro hx
      exact ⟨x - shift, hx, by ring⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [translateIntegerSet] using hy
  rw [hset, Set.ncard_image_of_injective]
  intro left right heq
  exact add_right_cancel heq

/-- Center a target list before translating an `h`-fold basis by `shift`. -/
def centerTargets (h : Nat) (shift : Int) (targets : List Int) : List Int :=
  targets.map fun target => target - (h : Int) * shift

@[simp]
theorem length_centerTargets (h : Nat) (shift : Int) (targets : List Int) :
    (centerTargets h shift targets).length = targets.length := by
  simp [centerTargets]

/-- The centered index corresponding to an index of the original list. -/
def centerTargetsIndex {targets : List Int} (h : Nat) (shift : Int)
    (index : Fin targets.length) :
    Fin (centerTargets h shift targets).length :=
  Fin.cast (by simp) index

@[simp]
theorem get_centerTargets_centerTargetsIndex {targets : List Int}
    (h : Nat) (shift : Int) (index : Fin targets.length) :
    (centerTargets h shift targets).get (centerTargetsIndex h shift index) =
      targets.get index - (h : Int) * shift := by
  simp [centerTargetsIndex, centerTargets]

/-- Membership in a centered target set is membership in the original set
after undoing the `h`-fold translation. -/
theorem mem_prescribedTargets_centerTargets_sub_iff
    {targets : List Int} {h : Nat} {shift x : Int} :
    Membership.mem (prescribedTargets (centerTargets h shift targets))
        (x - (h : Int) * shift) <->
      Membership.mem (prescribedTargets targets) x := by
  rw [mem_prescribedTargets_iff_mem, mem_prescribedTargets_iff_mem]
  simp [centerTargets]

/-- Set-level isolation pattern for arbitrary fold order. -/
def HasIsolatedExceptionalPattern
    (targets : List Int) (basis : Set Int) (h d : Nat) : Prop :=
  And
    (forall index : Fin targets.length,
      Membership.mem (hFoldSumset basis h) (targets.get index))
    (And
      (forall x,
        Membership.mem (hFoldSumset basis h) x ->
          Not (Membership.mem (prescribedTargets targets) x) ->
            forall index : Fin targets.length,
              d <= (x - targets.get index).natAbs)
      (forall x,
        Membership.mem (hFoldSumset basis h) x ->
          Not (Membership.mem (prescribedTargets targets) x) ->
            forall y,
              Membership.mem (hFoldSumset basis h) y ->
                Not (x = y) -> d <= (x - y).natAbs))

/-- Translating a centered isolated pattern restores the original target
list. -/
theorem hasIsolatedExceptionalPattern_translateIntegerSet
    {targets : List Int} {basis : Set Int} {h d : Nat} (shift : Int)
    (hpattern :
      HasIsolatedExceptionalPattern (centerTargets h shift targets) basis h d) :
    HasIsolatedExceptionalPattern targets (translateIntegerSet shift basis) h d := by
  rw [HasIsolatedExceptionalPattern] at hpattern
  rw [HasIsolatedExceptionalPattern]
  obtain ⟨htargets, htargetGaps, hexceptionalGaps⟩ := hpattern
  refine ⟨?_, ?_, ?_⟩
  · intro index
    rw [mem_hFoldSumset_translateIntegerSet_iff]
    have htarget := htargets (centerTargetsIndex h shift index)
    rw [get_centerTargets_centerTargetsIndex] at htarget
    exact htarget
  · intro x hx hxExceptional index
    rw [mem_hFoldSumset_translateIntegerSet_iff] at hx
    have hxCentered :
        Not (Membership.mem
          (prescribedTargets (centerTargets h shift targets))
          (x - (h : Int) * shift)) := by
      rwa [mem_prescribedTargets_centerTargets_sub_iff]
    have hgap :=
      htargetGaps (x - (h : Int) * shift) hx hxCentered
        (centerTargetsIndex h shift index)
    rw [get_centerTargets_centerTargetsIndex] at hgap
    convert hgap using 1
    ring_nf
  · intro x hx hxExceptional y hy hne
    rw [mem_hFoldSumset_translateIntegerSet_iff] at hx hy
    have hxCentered :
        Not (Membership.mem
          (prescribedTargets (centerTargets h shift targets))
          (x - (h : Int) * shift)) := by
      rwa [mem_prescribedTargets_centerTargets_sub_iff]
    have hneCentered :
        Not (x - (h : Int) * shift = y - (h : Int) * shift) := by
      intro heq
      apply hne
      linarith
    have hgap :=
      hexceptionalGaps (x - (h : Int) * shift) hx hxCentered
        (y - (h : Int) * shift) hy hneCentered
    convert hgap using 1
    ring_nf

/-- An isolated pattern on flattened separated intervals has exactly the
listed nontrivial intervals. -/
theorem hasIsolatedExceptionalPattern_hasExactlyNontrivialIntervals
    {starts : List Int} {n h d : Nat} {basis : Set Int}
    (hsep : SeparatedStarts starts n) (hd : 2 <= d)
    (hpattern :
      HasIsolatedExceptionalPattern (intervalTargets starts n) basis h d) :
    HasExactlyNontrivialIntervals (hFoldSumset basis h) starts n := by
  rw [HasIsolatedExceptionalPattern] at hpattern
  constructor
  · intro start hstart x hx
    have hxTarget :
        Membership.mem (prescribedTargets (intervalTargets starts n)) x := by
      rw [prescribedTargets_intervalTargets]
      exact ⟨start, hstart, hx.1, hx.2⟩
    have hxList :
        x ∈ intervalTargets starts n :=
      mem_prescribedTargets_iff_mem.mp hxTarget
    obtain ⟨index, hindex⟩ := List.get_of_mem hxList
    simpa only [hindex] using hpattern.1 index
  · intro x hx hxSucc
    have hxTarget :
        Membership.mem (prescribedTargets (intervalTargets starts n)) x := by
      by_contra hxExceptional
      have hgap := hpattern.2.2 x hx hxExceptional (x + 1) hxSucc (by omega)
      norm_num at hgap
      omega
    have hxSuccTarget :
        Membership.mem (prescribedTargets (intervalTargets starts n)) (x + 1) := by
      by_contra hxSuccExceptional
      have hgap := hpattern.2.2 (x + 1) hxSucc hxSuccExceptional x hx (by omega)
      norm_num at hgap
      omega
    rw [prescribedTargets_intervalTargets] at hxTarget hxSuccTarget
    exact exists_interval_of_mem_intervalUnion_of_succ_mem hsep hxTarget hxSuccTarget

end IntervalBases
