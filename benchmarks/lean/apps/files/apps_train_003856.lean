-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def iq_test (input : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem iq_test_edge_position_start :
  iq_test "1 2 2 2" = 1 ∧ 
  iq_test "2 1 1 1" = 1 :=
sorry

theorem iq_test_edge_position_end :
  iq_test "2 2 2 1" = 4 ∧
  iq_test "1 1 1 2" = 4 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval iq_test "2 4 7 8 10"

/-
info: 2
-/
-- #guard_msgs in
-- #eval iq_test "1 2 1 1"

/-
info: 3
-/
-- #guard_msgs in
-- #eval iq_test "5 3 2"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible