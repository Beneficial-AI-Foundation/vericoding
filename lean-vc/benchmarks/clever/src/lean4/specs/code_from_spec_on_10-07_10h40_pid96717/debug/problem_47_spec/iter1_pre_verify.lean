import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: Rat) :=
  0 < numbers.length →
  let less_eq := (numbers.filter (fun x => x ≤ result));
  let more_eq := (numbers.filter (fun x => result ≤ x));
  let max_more_eq := more_eq.max?;
  let min_less_eq := less_eq.min?;
  let less_eq_count := less_eq.length;
  let more_eq_count := more_eq.length;
  let eq_count := (numbers.filter (fun x => x = result)).length;
  (less_eq_count + more_eq_count - eq_count = numbers.length →
  numbers.length ≤ 2 * less_eq_count →
  numbers.length ≤ 2 * more_eq_count) ∧
  ((numbers.length % 2 = 1 →
    result ∈ numbers) ∧
    (numbers.length % 2 = 0 → max_more_eq.isSome ∧
    min_less_eq.isSome ∧
    2 * result = max_more_eq.get! + min_less_eq.get!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def quickselect (numbers: List Rat) (k: Nat) : Rat :=
  if h : k < numbers.length then
    let sorted := numbers.mergeSort (· ≤ ·)
    sorted.get ⟨k, by simp [List.length_mergeSort]; exact h⟩
  else
    0

def implementation (numbers: List Rat) : Rat := 
  if numbers.length = 0 then 0
  else if numbers.length % 2 = 1 then
    quickselect numbers (numbers.length / 2)
  else
    let mid1 := quickselect numbers (numbers.length / 2 - 1)
    let mid2 := quickselect numbers (numbers.length / 2)
    (mid1 + mid2) / 2

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · intro h
    simp [implementation]
    split_ifs with h1 h2
    · contradiction
    · simp [quickselect]
      split_ifs with h3
      · sorry
      · simp at h3
        omega
    · simp [quickselect]
      split_ifs with h3 h4
      · sorry
      · simp at h3
        omega
      · simp at h4
        omega
      · simp at h3 h4
        omega