-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>