-- <vc-preamble>
def factorial (n : Nat) : Nat :=
  sorry

def countTrailingZeroes (n : Nat) : Nat := 
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
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

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_trailing_zeroes 3

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_trailing_zeroes 5

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_trailing_zeroes 10
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded