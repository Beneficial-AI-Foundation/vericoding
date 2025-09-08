import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (number: Rat) : Rat :=
  number - number.floor

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

-- LLM HELPER
lemma sub_floor_nonneg (q : Rat) : 0 ≤ q - q.floor := by
  rw [sub_nonneg]
  exact Rat.floor_le q

-- LLM HELPER  
lemma sub_floor_lt_one (q : Rat) : q - q.floor < 1 := by
  rw [sub_lt_iff_lt_add]
  exact Rat.lt_floor_add_one q

theorem correctness
(number: Rat)
: problem_spec implementation number := by
  intro h_pos
  use number - number.floor
  constructor
  · rfl
  · constructor
    · exact sub_floor_nonneg number
    · constructor
      · exact sub_floor_lt_one number
      · ring