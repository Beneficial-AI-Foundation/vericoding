-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toothpick (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem toothpick_non_negative (n : Nat) :
  toothpick n ≥ 0 :=
  sorry

theorem toothpick_monotonic {n : Nat} (h : n > 0) : 
  toothpick n > toothpick (n-1) :=
  sorry

theorem toothpick_doubles {n : Nat} (h : n > 0) :
  toothpick (2^n) > 2 * toothpick (2^(n-1)) :=
  sorry

theorem toothpick_zero :
  toothpick 0 = 0 :=
  sorry
-- </vc-theorems>