-- <vc-helpers>
-- </vc-helpers>

def isPrime (n : Int) : Bool := sorry

def solve (a b : Int) : Int := sorry

theorem prime_properties (n : Int) : 
  isPrime n → n > 1 ∧ 
  (n > 2 ∧ n % 2 = 0 → ¬isPrime n) ∧
  (n = 2 → isPrime n) ∧ 
  (n < 2 → ¬isPrime n) := sorry

theorem solve_properties (a b : Int) :
  let b' := max a b
  solve a b' ≥ 0 ∧
  (b' ≤ a → solve a b' = 0) ∧
  (0 ≤ a ∧ a ≤ b' ∧ b' ≤ 2 → solve a b' = 0) ∧
  (a ≤ 2 ∧ 2 < b' ∧ b' ≤ 3 → solve a b' = 0) := sorry

/-
info: 14
-/
-- #guard_msgs in
-- #eval solve 0 20

/-
info: 457
-/
-- #guard_msgs in
-- #eval solve 2 200

/-
info: 25005
-/
-- #guard_msgs in
-- #eval solve 2000 5000

-- Apps difficulty: introductory
-- Assurance level: guarded