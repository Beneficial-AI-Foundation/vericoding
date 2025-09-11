-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_salary (x : Nat) (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_salary_positive (x n : Nat) (h₁ : x > 0) (h₂ : n > 0) :
  calculate_salary x n ≥ 0 :=
sorry

theorem calculate_salary_arithmetic_sum (x n : Nat) (h₁ : x > 0) (h₂ : n > 0) :
  calculate_salary x n = (List.range ((n + 1) / x)).foldl (fun acc i => acc + (i * x)) 0 :=
sorry 

theorem calculate_salary_greater_than_n (x n : Nat) (h : x > n) :
  calculate_salary x n = 0 :=
sorry

/-
info: 18
-/
-- #guard_msgs in
-- #eval calculate_salary 3 10

/-
info: 30
-/
-- #guard_msgs in
-- #eval calculate_salary 2 10

/-
info: 50
-/
-- #guard_msgs in
-- #eval calculate_salary 5 20
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded