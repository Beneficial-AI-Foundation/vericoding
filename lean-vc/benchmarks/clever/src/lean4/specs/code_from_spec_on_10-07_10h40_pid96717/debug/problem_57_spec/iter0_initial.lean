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
def is_monotonic (numbers: List Int) : Bool :=
  match numbers with
  | [] => true
  | [_] => true
  | x :: y :: rest =>
    if x ≤ y then is_monotonic (y :: rest)
    else if x ≥ y then is_monotonic_desc (y :: rest)
    else false
where
  is_monotonic_desc (numbers: List Int) : Bool :=
    match numbers with
    | [] => true
    | [_] => true
    | x :: y :: rest =>
      if x ≥ y then is_monotonic_desc (y :: rest)
      else false

def implementation (numbers: List Int) : Bool := is_monotonic numbers

-- LLM HELPER
lemma non_ordered_iff_not_monotonic (numbers: List Int) :
  let non_ordered := ∃ i j,
    i < numbers.length - 1 ∧
    j < numbers.length - 1 ∧
    (numbers[i]! < numbers[i+1]!) ∧
    (numbers[j+1]! < numbers[j]!)
  1 < numbers.length → (¬non_ordered ↔ is_monotonic numbers) := by
  sorry

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use is_monotonic numbers
  constructor
  · rfl
  · exact non_ordered_iff_not_monotonic numbers