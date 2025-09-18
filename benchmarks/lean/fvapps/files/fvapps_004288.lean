-- <vc-preamble>
def solve (n : Nat) : Nat :=
  sorry

def sumOfDigits (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPowerOfTen (n : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_result_bounded (n : Nat) (h : n > 0) : 
  let result := solve n
  result ≥ 0 ∧ result ≤ n :=
sorry

/-
info: 99
-/
-- #guard_msgs in
-- #eval solve 100

/-
info: 48
-/
-- #guard_msgs in
-- #eval solve 48

/-
info: 999
-/
-- #guard_msgs in
-- #eval solve 1000
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible