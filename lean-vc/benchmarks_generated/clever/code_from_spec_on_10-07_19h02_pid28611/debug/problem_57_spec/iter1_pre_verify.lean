import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → Bool)
-- inputs
(numbers: List Int) :=
let non_ordered := ∃ i j,
i < numbers.length - 1 ∧
j < numbers.length - 1 ∧
(numbers[i]! < numbers[i+1]!) ∧
(numbers[j+1]! < numbers[j]!);
-- spec
let spec (result: Bool) :=
  1 < numbers.length →
  result ↔ ¬non_ordered;
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def is_monotonic_increasing (numbers: List Int) : Bool :=
  numbers.zip (numbers.tail) |>.all (fun (a, b) => a ≤ b)

-- LLM HELPER
def is_monotonic_decreasing (numbers: List Int) : Bool :=
  numbers.zip (numbers.tail) |>.all (fun (a, b) => a ≥ b)

def implementation (numbers: List Int) : Bool := 
  is_monotonic_increasing numbers || is_monotonic_decreasing numbers

-- LLM HELPER
lemma non_ordered_iff_not_monotonic (numbers: List Int) :
  (∃ i j, i < numbers.length - 1 ∧ j < numbers.length - 1 ∧ 
   (numbers[i]! < numbers[i+1]!) ∧ (numbers[j+1]! < numbers[j]!)) ↔
  ¬(is_monotonic_increasing numbers || is_monotonic_decreasing numbers) := by
  sorry

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  simp only [exists_prop]
  constructor
  · rfl
  · intro h
    apply non_ordered_iff_not_monotonic