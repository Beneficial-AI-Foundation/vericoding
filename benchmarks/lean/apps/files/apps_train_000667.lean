-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_chef_transport (n v1 v2 : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_chef_transport_output_type (n v1 v2 : Nat) :
  n > 0 → v1 > 0 → v2 > 0 →
  solve_chef_transport n v1 v2 = "Stairs" ∨ 
  solve_chef_transport n v1 v2 = "Elevator" :=
sorry

theorem solve_chef_transport_deterministic (n v1 v2 : Nat) :
  n > 0 → v1 > 0 → v2 > 0 →
  solve_chef_transport n v1 v2 = solve_chef_transport n v1 v2 :=
sorry

/-
info: 'Elevator'
-/
-- #guard_msgs in
-- #eval solve_chef_transport 5 10 15

/-
info: 'Stairs'
-/
-- #guard_msgs in
-- #eval solve_chef_transport 2 10 14

/-
info: 'Stairs'
-/
-- #guard_msgs in
-- #eval solve_chef_transport 7 14 10
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded