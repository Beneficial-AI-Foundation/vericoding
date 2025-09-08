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
          decide (i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ numbers[i]! + numbers[j]! + numbers[k]! = 0)

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
lemma hasTripleSum_iff (numbers : List Int) :
  hasTripleSum numbers = true ↔ 
  3 ≤ numbers.length ∧ (∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
   i < numbers.length ∧ j < numbers.length ∧ k < numbers.length ∧
   numbers[i]! + numbers[j]! + numbers[k]! = 0) := by
  unfold hasTripleSum
  constructor
  · intro h
    by_cases h_len : numbers.length < 3
    · simp only [if_pos h_len] at h
    · push_neg at h_len
      simp only [if_neg h_len, List.any_eq_true, List.mem_range] at h
      constructor
      · exact h_len
      · obtain ⟨i, hi, j, hj, k, hk, h_cond⟩ := h
        use i, j, k
        rw [decide_eq_true_iff] at h_cond
        exact ⟨h_cond.1, h_cond.2.1, h_cond.2.2.1, hi, hj, hk, h_cond.2.2.2⟩
  · intro ⟨h_len, i, j, k, hij, hik, hjk, hi, hj, hk, h_sum⟩
    simp only [if_neg (not_lt.mpr h_len)]
    rw [List.any_eq_true, List.mem_range]
    use i, hi, j, hj, k, hk
    rw [decide_eq_true_iff]
    exact ⟨hij, hik, hjk, h_sum⟩

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use hasTripleSum numbers
  constructor
  · rfl
  · intro result
    constructor
    · intro h
      rw [hasTripleSum_iff] at h
      exact h
    · intro h
      rw [hasTripleSum_iff]
      exact h