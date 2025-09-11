-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_efficiency_workgroup (n : Nat) (superiors : List Int) (efficiencies : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_node_case (efficiency : Int) (h : -100 ≤ efficiency ∧ efficiency ≤ 100) :
  max_efficiency_workgroup 1 [-1] [efficiency] = efficiency :=
sorry

/-
info: 17
-/
-- #guard_msgs in
-- #eval max_efficiency_workgroup 7 [-1, 1, 1, 1, 4, 4, 5] [3, 2, 1, 4, 5, 3, 2]

/-
info: 42
-/
-- #guard_msgs in
-- #eval max_efficiency_workgroup 1 [-1] [42]

/-
info: 85
-/
-- #guard_msgs in
-- #eval max_efficiency_workgroup 3 [-1, 1, 1] [1, 42, 42]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible