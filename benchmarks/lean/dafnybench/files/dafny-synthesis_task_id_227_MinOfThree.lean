-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MinOfThree (a b c : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem MinOfThree_spec (a b c : Int) :
let min := MinOfThree a b c
min ≤ a ∧ min ≤ b ∧ min ≤ c ∧ (min = a ∨ min = b ∨ min = c) :=
sorry
-- </vc-theorems>