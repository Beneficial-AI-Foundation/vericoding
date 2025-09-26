-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factorial (n : Nat) : Nat :=
  sorry

def countTrailingZeroes (n : Nat) : Nat :=
  sorry

def countActualZeros (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_matches_actual {n : Nat} (h : n ≤ 1000) :
  countTrailingZeroes n = countActualZeros (factorial n) := by
  sorry

theorem count_non_negative (n : Nat) :
  countTrailingZeroes n ≥ 0 := by
  sorry

theorem count_less_than_five {n : Nat} (h : n < 5) :
  countTrailingZeroes n = 0 := by
  sorry

theorem count_zero :
  countTrailingZeroes 0 = 0 := by
  sorry

theorem count_one :
  countTrailingZeroes 1 = 0 := by
  sorry
-- </vc-theorems>