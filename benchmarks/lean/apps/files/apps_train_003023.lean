-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_alive (health : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_alive_returns_bool (health : Int) :
  check_alive health = true ∨ check_alive health = false :=
  sorry

theorem check_alive_positive_health (health : Int) :
  check_alive health ↔ health > 0 :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval check_alive 5

/-
info: False
-/
-- #guard_msgs in
-- #eval check_alive 0

/-
info: False
-/
-- #guard_msgs in
-- #eval check_alive -5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded