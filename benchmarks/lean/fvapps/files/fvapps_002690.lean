-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def power_law (p1 p2 : List Float) (x3 : Float) : Float := sorry

theorem power_law_identity (value : Float) (h1 : value ≥ 1) (h2 : value ≤ 100) :
  power_law [value, value] [value, value] value = value := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem power_law_examples :
  power_law [1, 120] [2, 60] 4 = 30 ∧
  power_law [1, 81] [2, 27] 4 = 9 ∧
  power_law [4, 30] [2, 60] 1 = 120 := sorry
-- </vc-theorems>