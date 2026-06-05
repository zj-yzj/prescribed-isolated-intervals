import Formalization.GenericLabels
import Mathlib.Data.ZMod.Basic

/-!
# Shifted Sidon labels for double sumsets

For `h = 2`, the generic construction only needs to exclude nonzero label
relations of l1 norm at most four.  The paper obtains this from explicit
shifted Sidon labels.  This file records the reusable Lean interface between
short-relation freedom and the abstract separated-label construction, together
with the explicit label formula and its elementary size bounds.
-/

namespace IntervalBases

/-- No nonzero coefficient function of l1 norm at most `L` evaluates to zero
against the given labels. -/
def ShortRelationFree {m : Nat} (labels : Fin m -> Int) (L : Nat) : Prop :=
  forall {coefficients : Fin m -> Int},
    Not (coefficients = 0) ->
      functionL1Norm coefficients <= L ->
        Not (linearLabelValue labels coefficients = 0)

theorem linearLabelValue_functionDifference {m : Nat}
    (labels xs ys : Fin m -> Int) :
    linearLabelValue labels (functionDifference xs ys) =
      linearLabelValue labels xs - linearLabelValue labels ys := by
  rw [linearLabelValue, linearLabelValue, linearLabelValue]
  calc
    (Finset.univ.sum fun index => functionDifference xs ys index * labels index) =
        Finset.univ.sum fun index =>
          xs index * labels index - ys index * labels index := by
      apply Finset.sum_congr rfl
      intro index _
      simp only [functionDifference]
      ring
    _ = (Finset.univ.sum fun index => xs index * labels index) -
        Finset.univ.sum fun index => ys index * labels index :=
      by rw [Finset.sum_sub_distrib]

theorem linearLabelValue_scaledLabels {m M : Nat}
    (labels coefficients : Fin m -> Int) :
    linearLabelValue (fun index => (M : Int) * labels index) coefficients =
      (M : Int) * linearLabelValue labels coefficients := by
  rw [linearLabelValue, linearLabelValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

theorem scale_le_natAbs_mul_of_ne_zero {M : Nat} {value : Int}
    (hne : Not (value = 0)) :
    M <= ((M : Int) * value).natAbs := by
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  calc
    M = M * 1 := by simp
    _ <= M * value.natAbs :=
      Nat.mul_le_mul_left M (Int.natAbs_pos.mpr hne)

/-- Scaling a short-relation-free family gives the separation property used
by the generic isolated-target theorem. -/
theorem scaledLabels_boundedLabelSeparation_of_shortRelationFree
    {m L M : Nat} {labels : Fin m -> Int}
    (hfree : ShortRelationFree labels L) :
    BoundedLabelSeparation (fun index => (M : Int) * labels index) L M := by
  intro xs ys hne hnorm
  rw [linearLabelValue_scaledLabels, linearLabelValue_scaledLabels, ← mul_sub,
    ← linearLabelValue_functionDifference]
  exact scale_le_natAbs_mul_of_ne_zero <|
    hfree (functionDifference_ne_zero_of_ne hne)
      ((functionL1Norm_functionDifference_le xs ys).trans hnorm)

/-- The natural-valued shifted Sidon label from the paper. -/
def shiftedSidonNatLabel (p r : Nat) : Nat :=
  2 * p ^ 2 + 2 * p * r + r ^ 2 % p

/-- The same shifted Sidon label, coerced to the integer type used by the
generic construction. -/
def shiftedSidonLabel (p r : Nat) : Int :=
  shiftedSidonNatLabel p r

theorem shiftedSidonNatLabel_lower_bound (p r : Nat) :
    2 * p ^ 2 <= shiftedSidonNatLabel p r := by
  simp only [shiftedSidonNatLabel]
  omega

theorem shiftedSidonNatLabel_upper_bound {p r : Nat} (hp : 0 < p)
    (hr : r < p) :
    shiftedSidonNatLabel p r < 4 * p ^ 2 := by
  have hmod : r ^ 2 % p < p := Nat.mod_lt _ hp
  simp only [shiftedSidonNatLabel]
  nlinarith

@[simp]
theorem shiftedSidonNatLabel_zero (p : Nat) :
    shiftedSidonNatLabel p 0 = 2 * p ^ 2 := by
  simp [shiftedSidonNatLabel]

/-- The gap from the zeroth shifted-Sidon label grows at least linearly in
the index. -/
theorem shiftedSidonNatLabel_sub_zero_lower_bound (p r : Nat) :
    2 * p * r <=
      shiftedSidonNatLabel p r - shiftedSidonNatLabel p 0 := by
  simp [shiftedSidonNatLabel]
  omega

/-- Equality of two shifted-Sidon pair sums determines both the index sum and
the sum of the quadratic residues. -/
theorem shiftedSidonNatLabel_pair_sum_components {p i j k l : Nat}
    (hp : 0 < p)
    (heq :
      shiftedSidonNatLabel p i + shiftedSidonNatLabel p j =
        shiftedSidonNatLabel p k + shiftedSidonNatLabel p l) :
    i + j = k + l /\ i ^ 2 % p + j ^ 2 % p = k ^ 2 % p + l ^ 2 % p := by
  have htwop : 0 < 2 * p := by omega
  have hiMod : i ^ 2 % p < p := Nat.mod_lt _ hp
  have hjMod : j ^ 2 % p < p := Nat.mod_lt _ hp
  have hkMod : k ^ 2 % p < p := Nat.mod_lt _ hp
  have hlMod : l ^ 2 % p < p := Nat.mod_lt _ hp
  have hleftResidue : i ^ 2 % p + j ^ 2 % p < 2 * p := by omega
  have hrightResidue : k ^ 2 % p + l ^ 2 % p < 2 * p := by omega
  have hdecomp (a b : Nat) :
      shiftedSidonNatLabel p a + shiftedSidonNatLabel p b =
        2 * p * (2 * p + a + b) + (a ^ 2 % p + b ^ 2 % p) := by
    simp only [shiftedSidonNatLabel]
    ring
  rw [hdecomp i j, hdecomp k l] at heq
  have hresidue :
      i ^ 2 % p + j ^ 2 % p = k ^ 2 % p + l ^ 2 % p := by
    have hmod := congrArg (fun value : Nat => value % (2 * p)) heq
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hleftResidue,
      Nat.mod_eq_of_lt hrightResidue] using hmod
  have hscaled :
      2 * p * (2 * p + i + j) = 2 * p * (2 * p + k + l) := by
    rw [hresidue] at heq
    exact Nat.add_right_cancel heq
  have hquotient :
      2 * p + i + j = 2 * p + k + l :=
    Nat.eq_of_mul_eq_mul_left htwop hscaled
  exact ⟨by omega, hresidue⟩

/-- The explicit shifted labels form a Sidon family on the index range below
an odd prime. Repetitions in a pair are allowed. -/
theorem shiftedSidonNatLabel_pair_sum_injective {p i j k l : Nat}
    (hprime : Nat.Prime p) (hodd : Not (p = 2))
    (hi : i < p) (hk : k < p) (hl : l < p)
    (heq :
      shiftedSidonNatLabel p i + shiftedSidonNatLabel p j =
        shiftedSidonNatLabel p k + shiftedSidonNatLabel p l) :
    (i = k /\ j = l) \/ (i = l /\ j = k) := by
  have hp : 0 < p := hprime.pos
  letI : Fact (Nat.Prime p) := ⟨hprime⟩
  obtain ⟨hsum, hresidue⟩ :=
    shiftedSidonNatLabel_pair_sum_components hp heq
  have hsumZ :
      (i : ZMod p) + (j : ZMod p) = (k : ZMod p) + (l : ZMod p) := by
    simpa only [Nat.cast_add] using
      congrArg (fun value : Nat => (value : ZMod p)) hsum
  have hsquareZ :
      (i : ZMod p) ^ 2 + (j : ZMod p) ^ 2 =
        (k : ZMod p) ^ 2 + (l : ZMod p) ^ 2 := by
    have hcast := congrArg (fun value : Nat => (value : ZMod p)) hresidue
    simpa only [Nat.cast_add, Nat.cast_pow, ZMod.natCast_mod] using hcast
  have htwo : Not ((2 : ZMod p) = 0) := by
    change Not (((2 : Nat) : ZMod p) = 0)
    rw [ZMod.natCast_eq_zero_iff]
    intro hpDividesTwo
    have hpLeTwo : p <= 2 := Nat.le_of_dvd (by omega) hpDividesTwo
    have hpTwoLe : 2 <= p := hprime.two_le
    omega
  have hprodZ :
      (i : ZMod p) * (j : ZMod p) = (k : ZMod p) * (l : ZMod p) := by
    apply mul_left_cancel₀ htwo
    calc
      (2 : ZMod p) * ((i : ZMod p) * (j : ZMod p)) =
          ((i : ZMod p) + (j : ZMod p)) ^ 2 -
            ((i : ZMod p) ^ 2 + (j : ZMod p) ^ 2) := by ring
      _ = ((k : ZMod p) + (l : ZMod p)) ^ 2 -
            ((k : ZMod p) ^ 2 + (l : ZMod p) ^ 2) := by
              rw [hsumZ, hsquareZ]
      _ = (2 : ZMod p) * ((k : ZMod p) * (l : ZMod p)) := by ring
  have hfactor :
      ((i : ZMod p) - (k : ZMod p)) * ((i : ZMod p) - (l : ZMod p)) = 0 := by
    calc
      ((i : ZMod p) - (k : ZMod p)) * ((i : ZMod p) - (l : ZMod p)) =
          (i : ZMod p) ^ 2 -
            (i : ZMod p) * ((k : ZMod p) + (l : ZMod p)) +
              (k : ZMod p) * (l : ZMod p) := by ring
      _ = (i : ZMod p) ^ 2 -
            (i : ZMod p) * ((i : ZMod p) + (j : ZMod p)) +
              (i : ZMod p) * (j : ZMod p) := by rw [hsumZ, hprodZ]
      _ = 0 := by ring
  rcases mul_eq_zero.mp hfactor with hik | hil
  · left
    have hikZ : (i : ZMod p) = (k : ZMod p) := sub_eq_zero.mp hik
    have hikVal := congrArg (fun value : ZMod p => value.val) hikZ
    have hikNat : i = k := by
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hk] using
        hikVal
    exact ⟨hikNat, by omega⟩
  · right
    have hilZ : (i : ZMod p) = (l : ZMod p) := sub_eq_zero.mp hil
    have hilVal := congrArg (fun value : ZMod p => value.val) hilZ
    have hilNat : i = l := by
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hl] using
        hilVal
    exact ⟨hilNat, by omega⟩

/-- A finite equality of short sums is trivial up to permutation. -/
def ShortListRelationFree {alpha : Type} (values : alpha -> Nat)
    (L : Nat) : Prop :=
  forall positive negative : List alpha,
    positive.length + negative.length <= L ->
      (positive.map values).sum = (negative.map values).sum ->
        positive.Perm negative

theorem length_mul_le_sum_map {alpha : Type} (values : alpha -> Nat)
    (C : Nat) (hlower : forall index, C <= values index) :
    forall indices : List alpha,
      indices.length * C <= (indices.map values).sum := by
  intro indices
  induction indices with
  | nil =>
      simp
  | cons index indices ih =>
      calc
        (index :: indices).length * C = C + indices.length * C := by
          simp [Nat.add_mul, Nat.add_comm]
        _ <= values index + (indices.map values).sum :=
          Nat.add_le_add (hlower index) ih
        _ = ((index :: indices).map values).sum := by simp

theorem sum_map_le_length_mul {alpha : Type} (values : alpha -> Nat)
    (U : Nat) (hupper : forall index, values index <= U) :
    forall indices : List alpha,
      (indices.map values).sum <= indices.length * U := by
  intro indices
  induction indices with
  | nil =>
      simp
  | cons index indices ih =>
      calc
        ((index :: indices).map values).sum =
            values index + (indices.map values).sum := by simp
        _ <= U + indices.length * U :=
          Nat.add_le_add (hupper index) ih
        _ = (index :: indices).length * U := by
          simp [Nat.add_mul, Nat.add_comm]

theorem sum_map_lt_length_mul_of_ne_nil {alpha : Type}
    (values : alpha -> Nat) (U : Nat)
    (hupper : forall index, values index < U) {indices : List alpha}
    (hne : Not (indices = [])) :
    (indices.map values).sum < indices.length * U := by
  cases indices with
  | nil =>
      exact (hne rfl).elim
  | cons index indices =>
      calc
        ((index :: indices).map values).sum =
            values index + (indices.map values).sum := by simp
        _ < U + indices.length * U :=
          Nat.add_lt_add_of_lt_of_le (hupper index)
            (sum_map_le_length_mul values U
              (fun tailIndex => Nat.le_of_lt (hupper tailIndex)) indices)
        _ = (index :: indices).length * U := by
          simp [Nat.add_mul, Nat.add_comm]

theorem shiftedSidonNatLabel_injective_of_lt_prime {p i k : Nat}
    (hprime : Nat.Prime p) (hodd : Not (p = 2))
    (hi : i < p) (hk : k < p)
    (heq : shiftedSidonNatLabel p i = shiftedSidonNatLabel p k) :
    i = k := by
  have hpairs :=
    shiftedSidonNatLabel_pair_sum_injective
      (i := i) (j := i) (k := k) (l := k)
      hprime hodd hi hk hk (by omega)
  rcases hpairs with hpairs | hpairs
  · exact hpairs.1
  · exact hpairs.1

/-- The shifted-Sidon labels have no nontrivial equality between sums using at
most four terms in total. This is the list-level form of the arithmetic input
needed by the double-sumset construction. -/
theorem shiftedSidonNatLabel_shortListRelationFree {p m : Nat}
    (hprime : Nat.Prime p) (hodd : Not (p = 2)) (hm : m <= p) :
    ShortListRelationFree
      (fun index : Fin m => shiftedSidonNatLabel p index.val) 4 := by
  let C := 2 * p ^ 2
  let values := fun index : Fin m => shiftedSidonNatLabel p index.val
  have hp : 0 < p := hprime.pos
  have hCpos : 0 < C := by
    simp only [C]
    positivity
  have hlower : forall index : Fin m, C <= values index := by
    intro index
    exact shiftedSidonNatLabel_lower_bound p index.val
  have hupper : forall index : Fin m, values index < 2 * C := by
    intro index
    have hindex : index.val < p := index.isLt.trans_le hm
    have hbound := shiftedSidonNatLabel_upper_bound hp hindex
    simp only [C, values]
    nlinarith
  intro positive negative hlength hsum
  change (positive.map values).sum = (negative.map values).sum at hsum
  by_cases hpositiveEmpty : positive = []
  · subst positive
    simp only [List.map_nil, List.sum_nil] at hsum
    have hnegativeEmpty : negative = [] := by
      by_contra hne
      have hnegativeLength : 0 < negative.length :=
        List.length_pos_of_ne_nil hne
      have hlowerSum := length_mul_le_sum_map values C hlower negative
      rw [← hsum] at hlowerSum
      simp only [nonpos_iff_eq_zero] at hlowerSum
      exact (Nat.mul_pos hnegativeLength hCpos).ne' hlowerSum
    subst negative
    exact List.Perm.refl []
  have hnegativeNonempty : Not (negative = []) := by
    intro hnegativeEmpty
    subst negative
    simp only [List.map_nil, List.sum_nil] at hsum
    have hpositiveLength : 0 < positive.length :=
      List.length_pos_of_ne_nil hpositiveEmpty
    have hlowerSum := length_mul_le_sum_map values C hlower positive
    rw [hsum] at hlowerSum
    simp only [nonpos_iff_eq_zero] at hlowerSum
    exact (Nat.mul_pos hpositiveLength hCpos).ne' hlowerSum
  have hpositiveLength : 0 < positive.length :=
    List.length_pos_of_ne_nil hpositiveEmpty
  have hnegativeLength : 0 < negative.length :=
    List.length_pos_of_ne_nil hnegativeNonempty
  have hpositiveLower := length_mul_le_sum_map values C hlower positive
  have hnegativeLower := length_mul_le_sum_map values C hlower negative
  have hpositiveUpper :=
    sum_map_lt_length_mul_of_ne_nil values (2 * C) hupper hpositiveEmpty
  have hnegativeUpper :=
    sum_map_lt_length_mul_of_ne_nil values (2 * C) hupper hnegativeNonempty
  have hsameLength : positive.length = negative.length := by
    rcases Nat.lt_trichotomy positive.length negative.length with hlt | heq | hgt
    · have hnegativeTwo : 2 <= negative.length := by omega
      have hpositiveOne : positive.length = 1 := by omega
      have htwoC : 2 * C <= negative.length * C :=
        Nat.mul_le_mul_right C hnegativeTwo
      rw [hpositiveOne, one_mul] at hpositiveUpper
      omega
    · exact heq
    · have hpositiveTwo : 2 <= positive.length := by omega
      have hnegativeOne : negative.length = 1 := by omega
      have htwoC : 2 * C <= positive.length * C :=
        Nat.mul_le_mul_right C hpositiveTwo
      rw [hnegativeOne, one_mul] at hnegativeUpper
      omega
  have hpositiveAtMostTwo : positive.length <= 2 := by omega
  have hlengthCases : positive.length = 1 \/ positive.length = 2 := by omega
  rcases hlengthCases with hlengthOne | hlengthTwo
  · obtain ⟨positiveIndex, rfl⟩ := List.length_eq_one_iff.mp hlengthOne
    have hnegativeLengthOne : negative.length = 1 := by omega
    obtain ⟨negativeIndex, rfl⟩ :=
      List.length_eq_one_iff.mp hnegativeLengthOne
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hsum
    have hval :
        positiveIndex.val = negativeIndex.val :=
      shiftedSidonNatLabel_injective_of_lt_prime hprime hodd
        (positiveIndex.isLt.trans_le hm) (negativeIndex.isLt.trans_le hm) hsum
    have hindex : positiveIndex = negativeIndex := Fin.ext hval
    subst negativeIndex
    exact List.Perm.refl [positiveIndex]
  · obtain ⟨positiveLeft, positiveRight, rfl⟩ :=
      List.length_eq_two.mp hlengthTwo
    have hnegativeLengthTwo : negative.length = 2 := by omega
    obtain ⟨negativeLeft, negativeRight, rfl⟩ :=
      List.length_eq_two.mp hnegativeLengthTwo
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hsum
    have hpairs :=
      shiftedSidonNatLabel_pair_sum_injective hprime hodd
        (positiveLeft.isLt.trans_le hm) (negativeLeft.isLt.trans_le hm)
        (negativeRight.isLt.trans_le hm) hsum
    rcases hpairs with hpairs | hpairs
    · have hleft : positiveLeft = negativeLeft := Fin.ext hpairs.1
      have hright : positiveRight = negativeRight := Fin.ext hpairs.2
      subst negativeLeft
      subst negativeRight
      exact List.Perm.refl [positiveLeft, positiveRight]
    · have hleft : positiveLeft = negativeRight := Fin.ext hpairs.1
      have hright : positiveRight = negativeLeft := Fin.ext hpairs.2
      subst negativeRight
      subst negativeLeft
      exact List.Perm.swap positiveRight positiveLeft []

/-- Expand the positive multiplicities of an integer coefficient function. -/
noncomputable def coefficientPositiveList {m : Nat} (coefficients : Fin m -> Int) :
    List (Fin m) :=
  Finset.univ.toList.flatMap fun index =>
    List.replicate (coefficients index).toNat index

/-- Expand the negative multiplicities of an integer coefficient function. -/
noncomputable def coefficientNegativeList {m : Nat} (coefficients : Fin m -> Int) :
    List (Fin m) :=
  Finset.univ.toList.flatMap fun index =>
    List.replicate (-coefficients index).toNat index

theorem length_coefficientPositiveList {m : Nat}
    (coefficients : Fin m -> Int) :
    (coefficientPositiveList coefficients).length =
      Finset.univ.sum fun index => (coefficients index).toNat := by
  classical
  simp [coefficientPositiveList]

theorem length_coefficientNegativeList {m : Nat}
    (coefficients : Fin m -> Int) :
    (coefficientNegativeList coefficients).length =
      Finset.univ.sum fun index => (-coefficients index).toNat := by
  classical
  simp [coefficientNegativeList]

theorem length_positive_add_length_negative {m : Nat}
    (coefficients : Fin m -> Int) :
    (coefficientPositiveList coefficients).length +
        (coefficientNegativeList coefficients).length =
      functionL1Norm coefficients := by
  classical
  rw [length_coefficientPositiveList, length_coefficientNegativeList,
    functionL1Norm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  exact Int.toNat_add_toNat_neg_eq_natAbs (coefficients index)

theorem sum_map_flatMap_replicate {alpha : Type} (values multiplicities : alpha -> Nat) :
    forall indices : List alpha,
      ((indices.flatMap fun index => List.replicate (multiplicities index) index).map
          values).sum =
        (indices.map fun index => multiplicities index * values index).sum := by
  intro indices
  induction indices with
  | nil =>
      simp
  | cons index indices ih =>
      simp [ih]

theorem sum_map_coefficientPositiveList {m : Nat} (values : Fin m -> Nat)
    (coefficients : Fin m -> Int) :
    ((coefficientPositiveList coefficients).map values).sum =
      Finset.univ.sum fun index => (coefficients index).toNat * values index := by
  classical
  rw [coefficientPositiveList, sum_map_flatMap_replicate]
  simp

theorem sum_map_coefficientNegativeList {m : Nat} (values : Fin m -> Nat)
    (coefficients : Fin m -> Int) :
    ((coefficientNegativeList coefficients).map values).sum =
      Finset.univ.sum fun index => (-coefficients index).toNat * values index := by
  classical
  rw [coefficientNegativeList, sum_map_flatMap_replicate]
  simp

theorem sum_positive_eq_sum_negative_of_linearLabelValue_eq_zero {m : Nat}
    (values : Fin m -> Nat) (coefficients : Fin m -> Int)
    (hzero :
      linearLabelValue (fun index => (values index : Int)) coefficients = 0) :
    ((coefficientPositiveList coefficients).map values).sum =
      ((coefficientNegativeList coefficients).map values).sum := by
  rw [sum_map_coefficientPositiveList, sum_map_coefficientNegativeList]
  have hdecomp :
      linearLabelValue (fun index => (values index : Int)) coefficients =
        (Finset.univ.sum fun index =>
          ((coefficients index).toNat : Int) * values index) -
        (Finset.univ.sum fun index =>
          ((-coefficients index).toNat : Int) * values index) := by
    rw [linearLabelValue, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro index _
    calc
      coefficients index * (values index : Int) =
          (((coefficients index).toNat : Int) -
            ((-coefficients index).toNat : Int)) * (values index : Int) := by
              rw [Int.toNat_sub_toNat_neg]
      _ = ((coefficients index).toNat : Int) * values index -
            ((-coefficients index).toNat : Int) * values index := by ring
  rw [hdecomp, sub_eq_zero] at hzero
  exact_mod_cast hzero

theorem count_coefficientPositiveList {m : Nat}
    (coefficients : Fin m -> Int) (index : Fin m) :
    List.count index (coefficientPositiveList coefficients) =
      (coefficients index).toNat := by
  classical
  simp only [coefficientPositiveList, List.count_flatMap]
  rw [Finset.sum_map_toList]
  calc
    Finset.univ.sum
        (List.count index ∘ fun other =>
          List.replicate (coefficients other).toNat other) =
        List.count index (List.replicate (coefficients index).toNat index) := by
      apply Finset.sum_eq_single index
      · intro other _ hne
        simp only [Function.comp_apply]
        rw [List.count_replicate]
        rw [if_neg]
        exact fun hbeq => hne (beq_iff_eq.mp hbeq)
      · simp
    _ = (coefficients index).toNat := by
      exact List.count_replicate_self

theorem count_coefficientNegativeList {m : Nat}
    (coefficients : Fin m -> Int) (index : Fin m) :
    List.count index (coefficientNegativeList coefficients) =
      (-coefficients index).toNat := by
  classical
  simp only [coefficientNegativeList, List.count_flatMap]
  rw [Finset.sum_map_toList]
  calc
    Finset.univ.sum
        (List.count index ∘ fun other =>
          List.replicate (-coefficients other).toNat other) =
        List.count index (List.replicate (-coefficients index).toNat index) := by
      apply Finset.sum_eq_single index
      · intro other _ hne
        simp only [Function.comp_apply]
        rw [List.count_replicate]
        rw [if_neg]
        exact fun hbeq => hne (beq_iff_eq.mp hbeq)
      · simp
    _ = (-coefficients index).toNat := by
      exact List.count_replicate_self

theorem coefficients_eq_zero_of_positiveList_perm_negativeList {m : Nat}
    {coefficients : Fin m -> Int}
    (hperm :
      (coefficientPositiveList coefficients).Perm
        (coefficientNegativeList coefficients)) :
    coefficients = 0 := by
  funext index
  have hcount := hperm.count_eq index
  rw [count_coefficientPositiveList, count_coefficientNegativeList] at hcount
  have hdecomp := Int.toNat_sub_toNat_neg (coefficients index)
  rw [hcount] at hdecomp
  simpa only [sub_self, Pi.zero_apply] using hdecomp.symm

/-- List-level freedom from short sum equalities implies the coefficient-vector
interface used by the generic construction. -/
theorem shortRelationFree_of_shortListRelationFree {m L : Nat}
    (values : Fin m -> Nat) (hlist : ShortListRelationFree values L) :
    ShortRelationFree (fun index => (values index : Int)) L := by
  intro coefficients hne hnorm hzero
  apply hne
  apply coefficients_eq_zero_of_positiveList_perm_negativeList
  apply hlist
  · rw [length_positive_add_length_negative]
    exact hnorm
  · exact sum_positive_eq_sum_negative_of_linearLabelValue_eq_zero
      values coefficients hzero

/-- The explicit shifted-Sidon labels satisfy the coefficient-vector
short-relation interface of order four. -/
theorem shiftedSidonLabel_shortRelationFree {p m : Nat}
    (hprime : Nat.Prime p) (hodd : Not (p = 2)) (hm : m <= p) :
    ShortRelationFree
      (fun index : Fin m => shiftedSidonLabel p index.val) 4 := by
  intro coefficients hne hnorm hzero
  exact
    shortRelationFree_of_shortListRelationFree
      (fun index : Fin m => shiftedSidonNatLabel p index.val)
      (shiftedSidonNatLabel_shortListRelationFree hprime hodd hm)
      hne hnorm hzero

/-- The set-level conclusion needed for a double-sumset isolated-target
construction. -/
def HasIsolatedExceptionalPatternH2 (targets : List Int) (basis : Set Int)
    (d : Nat) : Prop :=
  And
    (forall index : Fin targets.length,
      Membership.mem (hFoldSumset basis 2) (targets.get index))
    (And
      (forall x,
        Membership.mem (hFoldSumset basis 2) x ->
          Not (Membership.mem (prescribedTargets targets) x) ->
            forall index : Fin targets.length,
              d <= (x - targets.get index).natAbs)
      (forall x,
        Membership.mem (hFoldSumset basis 2) x ->
          Not (Membership.mem (prescribedTargets targets) x) ->
            forall y,
              Membership.mem (hFoldSumset basis 2) y ->
                Not (x = y) -> d <= (x - y).natAbs))

/-- Once short-relation freedom for a concrete Sidon family has been proved,
the complete set-level isolation theorem for double sumsets follows from the
generic construction. -/
theorem genericConstructedBasis_has_isolated_exceptional_pattern_h2_of_shortRelationFree
    {targets : List Int} {M T d : Nat}
    {labels : Fin targets.length -> Int}
    (htarget : forall index, (targets.get index).natAbs <= T)
    (hfree : ShortRelationFree labels 4)
    (hbudget : 4 * T + d <= M) :
    HasIsolatedExceptionalPatternH2 targets
      (genericConstructedBasis 2 targets
        (fun labelIndex => (M : Int) * labels labelIndex)) d := by
  rw [HasIsolatedExceptionalPatternH2]
  apply genericConstructedBasis_has_isolated_exceptional_pattern
    (h := 2) (M := M) (T := T) (d := d)
  · omega
  · exact htarget
  · intro xs ys hne hnorm
    exact
      scaledLabels_boundedLabelSeparation_of_shortRelationFree (M := M) hfree
        hne hnorm
  · omega

/-- The complete set-level isolation theorem for the explicit shifted-Sidon
labels. -/
theorem shiftedSidonLabels_have_isolated_exceptional_pattern
    {targets : List Int} {p M T d : Nat}
    (hprime : Nat.Prime p) (hodd : Not (p = 2)) (hm : targets.length <= p)
    (htarget : forall index, (targets.get index).natAbs <= T)
    (hbudget : 4 * T + d <= M) :
    HasIsolatedExceptionalPatternH2 targets
      (genericConstructedBasis 2 targets
        (fun index => (M : Int) * shiftedSidonLabel p index.val)) d :=
  genericConstructedBasis_has_isolated_exceptional_pattern_h2_of_shortRelationFree
    (M := M) htarget (shiftedSidonLabel_shortRelationFree hprime hodd hm) hbudget

end IntervalBases
