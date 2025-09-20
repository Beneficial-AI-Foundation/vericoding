-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def eq_solve (v0 v1 u0 u1 : Int) : Float := sorry

def min_operations (p q r a b c : Int) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem eq_solve_zero_denominator (v1 u1 : Int) :
  eq_solve 0 v1 0 u1 = 1 := sorry

theorem eq_solve_formula (v0 v1 u0 u1 : Int) :
  u0 ≠ v0 → eq_solve v0 v1 u0 u1 * Float.ofInt (u0 - v0) = Float.ofInt (u1 - v1) := sorry

theorem min_operations_bounds (p q r a b c : Int) :
  0 ≤ min_operations p q r a b c ∧ min_operations p q r a b c ≤ 3 := sorry

theorem min_operations_identity (x y z : Int) :
  min_operations x y z x y z = 0 := sorry

theorem min_operations_symmetry (p q r a b c : Int) :
  min_operations p q r a b c = min_operations r q p c b a := sorry
-- </vc-theorems>