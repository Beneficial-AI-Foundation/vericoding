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
  simp [add_sub_cancel_left]

-- LLM HELPER
lemma rat_fract_nonneg (r : Rat) : 0 ≤ r - r.floor := by
  have h : (r.floor : Rat) ≤ r := Int.floor_le r
  linarith

-- LLM HELPER
lemma rat_fract_lt_one (r : Rat) : r - r.floor < 1 := by
  have h : (r.floor : Rat) ≤ r := Int.floor_le r
  have h' : r < (r.floor : Rat) + 1 := Int.lt_floor_add_one r
  linarith

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