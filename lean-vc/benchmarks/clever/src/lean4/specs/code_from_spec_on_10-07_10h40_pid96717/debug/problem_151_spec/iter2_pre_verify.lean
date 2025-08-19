import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Rat → Int)
-- inputs
(numbers: List Rat) :=
let isEven (n : Rat) := n.num % 2 = 0;
let isNegative (n : Rat) := n < 0;
let isNotInteger (n : Rat) := n.den ≠ 1;
-- spec
let spec (result: Int) :=
0 < numbers.length →
0 ≤ result ∧
if numbers.length = 1
then result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2
else result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2 + impl numbers.tail
-- program terminates
∃ result, impl numbers = result ∧
-- return value satisfies spec
spec result

def implementation (numbers: List Rat) : Int := 
  if numbers.length = 0 then 0
  else
    let isEven (n : Rat) := n.num % 2 = 0
    let isNegative (n : Rat) := n < 0
    let isNotInteger (n : Rat) := n.den ≠ 1
    let head := numbers[0]!
    let contribution := if (isEven head ∨ isNegative head ∨ isNotInteger head) then 0 else head.floor ^ 2
    if numbers.length = 1 then contribution
    else contribution + implementation numbers.tail

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec
  let isEven (n : Rat) := n.num % 2 = 0
  let isNegative (n : Rat) := n < 0
  let isNotInteger (n : Rat) := n.den ≠ 1
  let spec (result: Int) :=
    0 < numbers.length →
    0 ≤ result ∧
    if numbers.length = 1
    then result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2
    else result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2 + implementation numbers.tail
  
  use implementation numbers
  constructor
  · rfl
  · intro h_pos_length
    unfold implementation
    split_ifs with h_empty
    · simp at h_empty
      simp at h_pos_length
      contradiction
    · constructor
      · -- Show result ≥ 0
        simp
      · -- Show the conditional equality
        simp