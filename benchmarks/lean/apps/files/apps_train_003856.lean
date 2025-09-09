-- <vc-helpers>
-- </vc-helpers>

def iq_test (input : String) : Nat :=
  sorry

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

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible