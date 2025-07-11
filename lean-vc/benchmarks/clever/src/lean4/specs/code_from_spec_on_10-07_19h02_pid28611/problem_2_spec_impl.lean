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
lemma floor_add_fract_eq (x : Rat) : x.floor + (x - x.floor) = x := by
  simp [add_sub_cancel_left]

-- LLM HELPER
lemma fract_nonneg (x : Rat) : 0 ≤ x - x.floor := by
  rw [sub_nonneg]
  exact Rat.floor_le x

-- LLM HELPER
lemma fract_lt_one (x : Rat) : x - x.floor < 1 := by
  rw [sub_lt_iff_lt_add]
  exact Rat.lt_floor_add_one x

theorem correctness
(number: Rat)
: problem_spec implementation number := by
  intro h
  use number - number.floor
  constructor
  · rfl
  · constructor
    · exact fract_nonneg number
    · constructor
      · exact fract_lt_one number
      · exact floor_add_fract_eq number