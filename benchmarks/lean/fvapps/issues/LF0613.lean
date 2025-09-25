-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_toggle_machines (N: Nat) (k: Nat) : State :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem toggle_base_case_one : 
  solve_toggle_machines 1 1 = State.ON :=
  sorry

theorem toggle_base_case_zero :
  solve_toggle_machines 1 0 = State.OFF :=
  sorry

theorem toggle_output_is_binary (N k: Nat) (h1: N > 0) (h2: N ≤ 10) :
  (solve_toggle_machines N k = State.ON) ∨ (solve_toggle_machines N k = State.OFF) :=
  sorry

theorem initial_state_is_off (N: Nat) (h: N > 0) (h2: N ≤ 10) :
  solve_toggle_machines N 0 = State.OFF :=
  sorry

theorem power_of_two_pattern (N k: Nat) (h1: N > 0) (h2: N ≤ 10) :
  (k + 1) % (2^N) = 0 → solve_toggle_machines N k = State.ON :=
  sorry

theorem power_of_two_pattern_converse (N k: Nat) (h1: N > 0) (h2: N ≤ 10) :
  (k + 1) % (2^N) ≠ 0 → solve_toggle_machines N k = State.OFF :=
  sorry

/-
info: 'OFF'
-/
-- #guard_msgs in
-- #eval solve_toggle_machines 4 0

/-
info: 'ON'
-/
-- #guard_msgs in
-- #eval solve_toggle_machines 4 47

/-
info: 'OFF'
-/
-- #guard_msgs in
-- #eval solve_toggle_machines 1 0

/-
info: 'ON'
-/
-- #guard_msgs in
-- #eval solve_toggle_machines 1 1
-- </vc-theorems>