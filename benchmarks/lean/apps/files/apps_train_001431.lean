-- <vc-helpers>
-- </vc-helpers>

def lcm (a b : Nat) : Nat := sorry

def solve_caterpillars (n : Nat) (lengths : List Nat) : Nat := sorry

theorem lcm_positive 
  (a b : Nat)
  (h1 : 1 ≤ a ∧ a ≤ 1000)
  (h2 : 1 ≤ b ∧ b ≤ 1000) :
  let r := lcm a b
  (r > 0) ∧ 
  (r % a = 0) ∧
  (r % b = 0) ∧
  (∀ x, 2 ≤ x ∧ x ≤ min a b → ¬((r/x) % a = 0 ∧ (r/x) % b = 0)) := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_caterpillars 20 [3, 2, 5]

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_caterpillars 10 [2, 3]

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve_caterpillars 15 [2, 3]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible