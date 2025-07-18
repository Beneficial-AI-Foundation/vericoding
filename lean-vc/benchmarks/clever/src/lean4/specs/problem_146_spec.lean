import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(nums: List Int) :=
-- spec
let spec (result: Int) :=
match nums with
| [] => result = 0
| head::tail =>
  let first_digit := (toString head.natAbs).toList[0]!.toNat - Char.toNat '0';
  let last_digit := head % 10;
  let valid := head > 10 ∧ Odd first_digit ∧ Odd last_digit
  if valid then result = 1 + impl tail else result = impl tail
-- program termination
∃ result, impl nums = result ∧
-- return value satisfies spec
spec result

def implementation (nums: List Int) : Int := sorry

theorem correctness
(nums: List Int)
: problem_spec implementation nums := sorry
