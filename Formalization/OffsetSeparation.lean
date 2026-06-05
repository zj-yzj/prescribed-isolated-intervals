import Formalization.PositionalSeparation

/-!
# Offsets preserve a controlled separation gap

The constructive proof uses positional labels together with bounded offsets.
This file formalizes the triangle-inequality step that turns label separation
into separation of the represented integers.
-/

namespace IntervalBases

/-- If two labels are at least `M` apart, their offsets differ by at most `R`,
and `M` includes a budget of `R + d`, then the represented integers are at
least `d` apart. -/
theorem offset_gap {M R d : Nat} {x y u v : Int}
    (hlabel : M <= (x - y).natAbs) (hoffset : (u - v).natAbs <= R)
    (hbudget : R + d <= M) :
    d <= ((u + x) - (v + y)).natAbs := by
  have htriangle :
      (x - y).natAbs <= ((u + x) - (v + y)).natAbs + (u - v).natAbs := by
    calc
      (x - y).natAbs = (((u + x) - (v + y)) - (u - v)).natAbs := by
        congr 1
        ring
      _ <= ((u + x) - (v + y)).natAbs + (u - v).natAbs :=
        Int.natAbs_sub_le _ _
  omega

/-- Combined form used by the interval-basis construction: distinct bounded
coefficient vectors remain separated after adding bounded offsets. -/
theorem offset_gap_of_distinct_scaledPositionalValues {M B R d : Nat}
    {xs ys : List Int} {u v : Int} (hlen : xs.length = ys.length)
    (hne : Not (xs = ys)) (hnorm : l1Norm xs + l1Norm ys <= B)
    (hoffset : (u - v).natAbs <= R) (hbudget : R + d <= M) :
    d <= ((u + scaledPositionalValue M B xs) -
      (v + scaledPositionalValue M B ys)).natAbs := by
  apply offset_gap
  · exact scale_le_natAbs_sub_scaledPositionalValue hlen hne hnorm
  · exact hoffset
  · exact hbudget

end IntervalBases

