import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → Bool)
(numbers: List Int) :=
let sum_i_j_k (i j k: Nat) : Bool :=
  numbers[i]! + numbers[j]! + numbers[k]! = 0;
let exists_zero := 3 ≤ numbers.length ∧ (∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
 i < numbers.length ∧ j < numbers.length ∧ k < numbers.length ∧
 sum_i_j_k i j k)
let spec (result: Bool) :=
result ↔ exists_zero
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def check_three_sum_aux (numbers: List Int) (i j k: Nat) : Bool :=
  if i < numbers.length ∧ j < numbers.length ∧ k < numbers.length then
    numbers[i]! + numbers[j]! + numbers[k]! = 0
  else
    false

-- LLM HELPER
def check_all_triplets (numbers: List Int) : Bool :=
  if numbers.length < 3 then false
  else
    let n := numbers.length
    (List.range n).any fun i =>
      (List.range n).any fun j =>
        (List.range n).any fun k =>
          i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ check_three_sum_aux numbers i j k

def implementation (numbers: List Int) : Bool := check_all_triplets numbers

-- LLM HELPER
lemma check_three_sum_aux_correct (numbers: List Int) (i j k: Nat) :
  check_three_sum_aux numbers i j k = true ↔ 
  (i < numbers.length ∧ j < numbers.length ∧ k < numbers.length ∧ 
   numbers[i]! + numbers[j]! + numbers[k]! = 0) := by
  simp [check_three_sum_aux]
  split_ifs with h
  · simp [h]
  · simp
    intro h1 h2 h3
    exact h ⟨h1, h2, h3⟩

-- LLM HELPER
lemma List.any_eq_true_iff {α : Type*} (l : List α) (p : α → Bool) :
  l.any p = true ↔ ∃ a ∈ l, p a = true := by
  simp [List.any_eq_true]

-- LLM HELPER
lemma List.mem_range_iff (n : Nat) (i : Nat) : i ∈ List.range n ↔ i < n := by
  simp [List.mem_range]

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers := by
  simp [problem_spec, implementation]
  use check_all_triplets numbers
  constructor
  · rfl
  · simp [check_all_triplets]
    split_ifs with h
    · simp
      push_neg
      intro h1 i j k hi hj hk hij hik hjk
      simp [List.any_eq_true_iff, List.mem_range_iff]
      push_neg
      use i, j, k
      simp [check_three_sum_aux_correct, hi, hj, hk]
    · simp
      constructor
      · intro h1
        linarith
      · intro h1 h2 i j k hij hik hjk hi hj hk hsum
        simp [List.any_eq_true_iff, List.mem_range_iff] at h1
        specialize h1 i hi j hj k hk
        simp [check_three_sum_aux_correct, hi, hj, hk] at h1
        exact h1 ⟨hij, hik, hjk, hsum⟩