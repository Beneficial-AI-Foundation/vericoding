-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def num_steps (s : String) : Nat := sorry

theorem num_steps_non_negative (s : String) (h : s.startsWith "1") : 
  num_steps s ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_one_zero_steps : 
  num_steps "1" = 0 := sorry

theorem min_steps_lower_bound (s : String) (h : s.startsWith "1") :
  num_steps s ≥ s.length - 1 := sorry

theorem ten_pattern_steps :
  num_steps "10" = 1 := sorry

theorem alternating_pattern_bound (n : Nat) (h : n ≥ 2) :
  let s := "1" ++ String.mk (List.join (List.replicate n ['0', '1']));
  num_steps s ≥ s.length := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval num_steps "1101"

/-
info: 1
-/
-- #guard_msgs in
-- #eval num_steps "10"

/-
info: 0
-/
-- #guard_msgs in
-- #eval num_steps "1"
-- </vc-theorems>