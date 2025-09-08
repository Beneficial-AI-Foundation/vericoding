import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def hasTripleSum (numbers: List Int) : Bool :=
  let n := numbers.length
  if n < 3 then false
  else
    (List.range n).any fun i =>
      (List.range n).any fun j =>
        (List.range n).any fun k =>
          i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ numbers[i]! + numbers[j]! + numbers[k]! = 0

def implementation (numbers: List Int) : Bool :=
  hasTripleSum numbers

def problem_spec
-- function signature
(implementation: List Int → Bool)
-- inputs
(numbers: List Int) :=
let sum_i_j_k (i j k: Nat) : Bool :=
  numbers[i]! + numbers[j]! + numbers[k]! = 0;
let exists_zero := 3 ≤ numbers.length ∧ (∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
 i < numbers.length ∧ j < numbers.length ∧ k < numbers.length ∧
 sum_i_j_k i j k)
-- spec
let spec (result: Bool) :=
result ↔ exists_zero
-- -- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma list_any_exists {α : Type*} (l : List α) (p : α → Bool) :
  l.any p = true ↔ ∃ x ∈ l, p x = true := by
  simp [List.any_eq_true]

-- LLM HELPER
lemma list_range_mem (n : Nat) (i : Nat) :
  i ∈ List.range n ↔ i < n := by
  simp [List.mem_range]

-- LLM HELPER
lemma hasTripleSum_iff (numbers : List Int) :
  hasTripleSum numbers = true ↔ 
  3 ≤ numbers.length ∧ (∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
   i < numbers.length ∧ j < numbers.length ∧ k < numbers.length ∧
   numbers[i]! + numbers[j]! + numbers[k]! = 0) := by
  unfold hasTripleSum
  split_ifs with h
  · simp
    constructor
    · intro h_false
      cases h_false
    · intro ⟨h_len, _⟩
      omega
  · simp [list_any_exists, list_range_mem]
    constructor
    · intro ⟨i, hi, j, hj, k, hk, h_cond⟩
      constructor
      · omega
      · exact ⟨i, j, k, h_cond.1, h_cond.2.1, h_cond.2.2.1, hi, hj, hk, h_cond.2.2.2⟩
    · intro ⟨h_len, i, j, k, hij, hik, hjk, hi, hj, hk, h_sum⟩
      exact ⟨i, hi, j, hj, k, hk, hij, hik, hjk, h_sum⟩

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  simp only [exists_prop]
  constructor
  · rfl
  · rw [hasTripleSum_iff]
    simp