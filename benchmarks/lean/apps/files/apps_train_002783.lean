-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def are_coprime (a b : Int) : Bool := sorry

theorem self_coprime (n : Int) : 
  are_coprime n n = (n.natAbs = 1) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem symmetry (n m : Int) : 
  are_coprime n m = are_coprime m n := sorry

theorem sign_invariance (n m : Int) :
  are_coprime n m = are_coprime n.natAbs m.natAbs := sorry

theorem multiplication_property (n m k : Int) :
  (are_coprime n m ∧ are_coprime n k) → are_coprime n (m * k) := sorry

theorem zero_coprime (n : Int) :
  are_coprime n 0 = (n.natAbs = 1) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval are_coprime 20 27

/-
info: False
-/
-- #guard_msgs in
-- #eval are_coprime 12 39

/-
info: True
-/
-- #guard_msgs in
-- #eval are_coprime 64 27
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded