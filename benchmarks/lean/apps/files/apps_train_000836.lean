-- <vc-helpers>
-- </vc-helpers>

def find_last_laddu (n : Nat) : Nat :=
sorry

theorem find_last_laddu_bounds (n : Nat) (h : n > 0) : 
  let result := find_last_laddu n
  0 < result ∧ result ≤ n := 
sorry

theorem find_last_laddu_next_power_exceeds (n : Nat) (h : n > 0) :
  let result := find_last_laddu n
  2 * result > n :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_last_laddu 1

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_last_laddu 5

/-
info: 8
-/
-- #guard_msgs in
-- #eval find_last_laddu 8

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible