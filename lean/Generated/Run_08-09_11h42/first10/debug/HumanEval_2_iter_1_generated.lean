/- 
function_signature: "def truncate_number(number: float) -> float"
docstring: |
    Given a positive floating point number, it can be decomposed into
    and integer part (largest integer smaller than given number) and decimals
    (leftover part always smaller than 1).

    Return the decimal part of the number.
test_cases:
  - input: 3.5
    expected_output: 0.5
-/

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
lemma fract_nonneg (x : Rat) : 0 ≤ x - x.floor := by
  have h : x.floor ≤ x := Rat.floor_le x
  linarith

-- LLM HELPER
lemma fract_lt_one (x : Rat) : x - x.floor < 1 := by
  have h : x < x.floor + 1 := Rat.lt_floor_add_one x
  linarith

-- LLM HELPER
lemma floor_add_fract (x : Rat) : x.floor + (x - x.floor) = x := by
  ring

theorem correctness
(number: Rat)
: problem_spec implementation number := by
  intro h_pos
  use number - number.floor
  constructor
  · rfl
  · constructor
    · exact fract_nonneg number
    constructor
    · exact fract_lt_one number
    · exact floor_add_fract number