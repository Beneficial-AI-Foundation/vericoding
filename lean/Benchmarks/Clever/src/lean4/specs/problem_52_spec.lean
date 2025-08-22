import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → Int → Bool)
(numbers: List Int)
(threshold: Int) :=
let numbers_below_threshold :=
  ∀ i, i < numbers.length → numbers[i]! < threshold;
let spec (res: Bool) :=
(numbers.length = 0 → res) ∧
(res ↔ numbers_below_threshold)
∃ result, implementation numbers threshold = result ∧
spec result

def implementation (numbers: List Int) (threshold: Int) : Bool := sorry

theorem correctness
(numbers: List Int)
(threshold: Int)
: problem_spec implementation numbers threshold := sorry 