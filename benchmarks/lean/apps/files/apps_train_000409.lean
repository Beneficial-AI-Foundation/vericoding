-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bulbSwitch (n : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bulb_switch_nonnegative (n : Int) (h : n ≥ 0) : 
  let result := bulbSwitch n
  result ≥ 0 ∧ result ≤ n :=
  sorry

theorem bulb_switch_negative (n : Int) (h : n < 0) :
  bulbSwitch n = -1 :=
  sorry

theorem bulb_switch_zero :
  bulbSwitch 0 = 0 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval bulb_switch 3

/-
info: 0
-/
-- #guard_msgs in
-- #eval bulb_switch 0

/-
info: 2
-/
-- #guard_msgs in
-- #eval bulb_switch 4
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded