import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Rat → Rat)
-- inputs
(number: Rat) :=
-- spec
let spec (res) :=
0 ≤ res ∧
res < 1 ∧
number.floor + res = number;
number > 0 →
-- program terminates
(∃ result, impl number = result ∧
-- return value satisfies spec
spec result)

def implementation (number: Rat) : Rat := number - number.floor

-- LLM HELPER
lemma rat_floor_add_fract_eq (r : Rat) : r.floor + (r - r.floor) = r := by
  simp [Rat.floor_add_fract]

-- LLM HELPER
lemma rat_fract_nonneg (r : Rat) : 0 ≤ r - r.floor := by
  rw [← Rat.fract_def]
  exact Rat.fract_nonneg r

-- LLM HELPER
lemma rat_fract_lt_one (r : Rat) : r - r.floor < 1 := by
  rw [← Rat.fract_def]
  exact Rat.fract_lt_one r

theorem correctness
(number: Rat)
: problem_spec implementation number := by
  intro h
  use number - number.floor
  constructor
  · rfl
  · constructor
    · exact rat_fract_nonneg number
    · constructor
      · exact rat_fract_lt_one number
      · exact rat_floor_add_fract_eq number