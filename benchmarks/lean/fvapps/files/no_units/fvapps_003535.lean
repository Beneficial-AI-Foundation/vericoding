-- <vc-preamble>
def array_change (arr : List Int) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum (l : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_change_returns_nonnegative (arr : List Int) (h : arr.length ≥ 1) :
  array_change arr ≥ 0 :=
  sorry
-- </vc-theorems>