-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def expression_matter (a b c : Nat) : Nat := sorry

theorem result_greater_than_inputs (a b c : Nat) 
  (h₁ : 1 ≤ a ∧ a ≤ 10) 
  (h₂ : 1 ≤ b ∧ b ≤ 10)
  (h₃ : 1 ≤ c ∧ c ≤ 10) :
  expression_matter a b c ≥ max a (max b c) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_greater_than_sum (a b c : Nat)
  (h₁ : 1 ≤ a ∧ a ≤ 10)
  (h₂ : 1 ≤ b ∧ b ≤ 10) 
  (h₃ : 1 ≤ c ∧ c ≤ 10) :
  expression_matter a b c ≥ a + b + c := sorry

theorem result_greater_than_min_products (a b c : Nat)
  (h₁ : 1 ≤ a ∧ a ≤ 10)
  (h₂ : 1 ≤ b ∧ b ≤ 10)
  (h₃ : 1 ≤ c ∧ c ≤ 10) :
  expression_matter a b c ≥ min (a*b*c) (min ((a+b)*c) (a*(b+c))) := sorry

theorem result_bounded_above (a b c : Nat)
  (h₁ : 1 ≤ a ∧ a ≤ 10)
  (h₂ : 1 ≤ b ∧ b ≤ 10)
  (h₃ : 1 ≤ c ∧ c ≤ 10) :
  expression_matter a b c ≤ max (a*b*c) (max (a+b+c) (max ((a+b)*c) (a*(b+c)))) := sorry

theorem result_equal_inputs (x : Nat)
  (h : 1 ≤ x ∧ x ≤ 10) :
  expression_matter x x x = max (x*x*x) (max (3*x) (2*x*x)) := sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval expression_matter 1 2 3

/-
info: 3
-/
-- #guard_msgs in
-- #eval expression_matter 1 1 1

/-
info: 18
-/
-- #guard_msgs in
-- #eval expression_matter 9 1 1
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible