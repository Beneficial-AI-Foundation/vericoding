-- <vc-preamble>
def countDivisors (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def divNum (a b : Nat) : Option Nat := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem divNum_invalid_range {a b : Nat} (h : a > b) : 
  divNum a b = none := 
  sorry

theorem divNum_result_in_range {a b : Nat} (h : a ≤ b) (result : Nat) :
  divNum a b = some result → a ≤ result ∧ result ≤ b :=
  sorry  

theorem divNum_max_divisors {a b result : Nat} (h : a ≤ b) :
  divNum a b = some result →
  ∀ x, a ≤ x ∧ x ≤ b → countDivisors x ≤ countDivisors result :=
  sorry

theorem divNum_equal_inputs (x : Nat) :
  divNum x x = some x :=
  sorry

/-
info: 24
-/
-- #guard_msgs in
-- #eval div_num 15 30

/-
info: 2
-/
-- #guard_msgs in
-- #eval div_num 1 2

/-
info: 'Error'
-/
-- #guard_msgs in
-- #eval div_num 159 4
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded