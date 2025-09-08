/- 
function_signature: "def sum_largest_prime(lst : list[int]) -> int"
docstring: |
    You are given a list of integers.
    You need to find the largest prime value and return the sum of its digits.
    Note(George): Modified to use List of nats because all examples are nats.
test_cases:
  - input: [0,3,2,1,3,5,7,4,5,5,5,2,181,32,4,32,3,2,32,324,4,3]
    expected_output: 10
  - input: [1,0,1,8,2,4597,2,1,3,40,1,2,1,2,4,2,5,1]
    expected_output: 25
  - input: [1,3,1,32,5107,34,83278,109,163,23,2323,32,30,1,9,3]
    expected_output: 13
  - input: [0,724,32,71,99,32,6,0,5,91,83,0,5,6]
    expected_output: 11
  - input: [0,81,12,3,1,21]
    expected_output: 3
  - input: [0,8,1,2,1,7]
    expected_output: 7
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def findLargestPrime (lst : List Nat) : Option Nat :=
  let primes := lst.filter Nat.Prime
  primes.foldl (fun acc x => if acc.isSome && acc.get! ≥ x then acc else some x) none

def implementation (lst: List Nat) : Nat :=
  match findLargestPrime lst with
  | none => 0
  | some prime => (Nat.digits 10 prime).sum

def problem_spec
-- function signature
(implementation: List Nat → Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : Nat) :=
  lst.any (fun num => decide (Nat.Prime num)) = true →
    result > 0 ∧ ∃ i, i < lst.length ∧ Nat.Prime (lst[i]!) ∧
    (∀ j, j < lst.length ∧ Nat.Prime (lst[j]!) → (lst[j]!) ≤ (lst[i]!)) ∧
    result = (Nat.digits 10 (lst[i]!)).sum
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
lemma findLargestPrime_spec (lst : List Nat) :
  match findLargestPrime lst with
  | none => ¬(lst.any (fun num => decide (Nat.Prime num)) = true)
  | some p => p ∈ lst ∧ Nat.Prime p ∧ ∀ x ∈ lst, Nat.Prime x → x ≤ p := by
  unfold findLargestPrime
  simp [List.any_eq_true, decide_eq_true_eq]
  sorry

-- LLM HELPER
lemma digits_sum_pos (n : Nat) (hn : n > 0) : (Nat.digits 10 n).sum > 0 := by
  have h : (Nat.digits 10 n).length > 0 := by
    rw [Nat.digits_len]
    simp [Nat.log_pos_iff]
    cases' n with n'
    · omega
    · norm_num
  have : (Nat.digits 10 n) ≠ [] := List.ne_nil_of_length_pos h
  cases' Nat.digits 10 n with head tail
  · contradiction
  · simp [List.sum_cons]
    omega

theorem correctness
(lst: List Nat)
: problem_spec implementation lst := by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · intro h_any_prime
    unfold implementation
    have h_spec := findLargestPrime_spec lst
    cases h_find : findLargestPrime lst with
    | none =>
      rw [h_find] at h_spec
      contradiction
    | some p =>
      rw [h_find] at h_spec
      simp
      constructor
      · apply digits_sum_pos
        have : p > 0 := Nat.Prime.pos h_spec.2.1
        exact this
      · have ⟨hp_mem, hp_prime, hp_max⟩ := h_spec
        obtain ⟨i, hi_mem_eq⟩ := List.mem_iff_get.mp hp_mem
        use i.val
        constructor
        · exact i.isLt
        constructor
        · rw [List.get_eq_getElem]
          rw [←hi_mem_eq]
          exact hp_prime
        constructor
        · intro j hj_lt hj_prime
          have : lst[j]! ≤ p := hp_max (lst[j]!) (List.getElem_mem lst j hj_lt) hj_prime
          rw [←hi_mem_eq]
          rw [List.get_eq_getElem] at hi_mem_eq
          rw [hi_mem_eq]
          exact this
        · rw [←hi_mem_eq]
          rw [List.get_eq_getElem] at hi_mem_eq
          rw [hi_mem_eq]

-- #test implementation [0,3,2,1,3,5,7,4,5,5,5,2,181,32,4,32,3,2,32,324,4,3] = 10
-- #test implementation [1,0,1,8,2,4597,2,1,3,40,1,2,1,2,4,2,5,1] = 25
-- #test implementation [1,3,1,32,5107,34,83278,109,163,23,2323,32,30,1,9,3] = 13
-- #test implementation [0,724,32,71,99,32,6,0,5,91,83,0,5,6] = 11
-- #test implementation [0,81,12,3,1,21] = 3
-- #test implementation [0,8,1,2,1,7] = 7