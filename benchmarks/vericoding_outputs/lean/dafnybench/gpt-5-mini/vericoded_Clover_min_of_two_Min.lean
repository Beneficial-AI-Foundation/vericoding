import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma LLM_le_of_lt {a b : Int} (h : a < b) : a ≤ b := le_of_lt h

-- LLM HELPER
lemma LLM_not_le_of_gt {a b : Int} (h : a > b) : ¬ a ≤ b := fun hle => lt_irrefl b (lt_of_lt_of_le h hle)
-- </vc-helpers>

-- <vc-definitions>
def Min_ (x y : Int) : Int :=
if x ≤ y then x else y
-- </vc-definitions>

-- <vc-theorems>
theorem Min_spec (x y z : Int) :
z = Min_ x y →
((x ≤ y → z = x) ∧
(x > y → z = y)) :=
by
  intro hz
  dsimp [Min_] at hz
  constructor
  · intro hxy
    rw [if_pos hxy] at hz
    exact hz
  · intro hxy
    have hnl := LLM_not_le_of_gt hxy
    rw [if_neg hnl] at hz
    exact hz
-- </vc-theorems>
