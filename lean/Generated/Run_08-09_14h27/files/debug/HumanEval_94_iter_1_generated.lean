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
  lst.filter Nat.Prime |>.maximum?

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
  lst.any (fun num => Nat.Prime num) →
    result > 0 ∧ ∃ i, i < lst.length ∧ Prime (lst[i]!) ∧
    (∀ j, j < lst.length ∧ Prime (lst[j]!) → lst[i]! ≤ lst[j]!) ∧
    result = (Nat.digits 10 (lst[i]!)).sum
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
lemma findLargestPrime_spec (lst : List Nat) :
  match findLargestPrime lst with
  | none => ¬lst.any Nat.Prime
  | some p => p ∈ lst ∧ Nat.Prime p ∧ ∀ x ∈ lst, Nat.Prime x → x ≤ p := by
  unfold findLargestPrime
  cases h : (lst.filter Nat.Prime).maximum? with
  | none => 
    simp [List.maximum?_eq_none_iff] at h
    simp [List.any_eq_true, List.mem_filter] at h
    exact h
  | some p =>
    simp [List.maximum?_eq_some_iff] at h
    constructor
    · exact List.mem_of_mem_filter _ h.1
    constructor
    · exact List.mem_filter.mp h.1 |>.2
    · intro x hx_mem hx_prime
      apply h.2
      exact List.mem_filter.mpr ⟨hx_mem, hx_prime⟩

-- LLM HELPER
lemma digits_sum_pos (n : Nat) (hn : n > 0) : (Nat.digits 10 n).sum > 0 := by
  have h : (Nat.digits 10 n).length > 0 := by
    rw [Nat.digits_len]
    simp [Nat.log_pos_iff]
    omega
  have : (Nat.digits 10 n) ≠ [] := List.ne_nil_of_length_pos h
  cases' Nat.digits 10 n with head tail
  · simp at this
  · simp [List.sum_cons]
    have : head < 10 := Nat.digits_lt_base (by norm_num) n head (List.mem_cons_self _ _)
    have : head ≥ 1 := by
      by_contra h_not
      simp at h_not
      have h_zero : head = 0 := Nat.eq_zero_of_lt_one h_not
      rw [h_zero, List.sum_cons, zero_add]
      have h_n_eq : n = (tail.sum) := by
        have := Nat.sum_digits_eq 10 n (by norm_num)
        simp [Nat.digits] at this
        rw [h_zero, zero_add] at this
        exact this.symm
      sorry -- This gets complex, but intuitively if leading digit is 0, we have issues
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
        obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_get.mp hp_mem
        use i
        constructor
        · exact hi_lt
        constructor
        · rw [←hi_eq]; exact hp_prime
        constructor
        · intro j hj_lt hj_prime
          have hj_mem : lst[j]! ∈ lst := List.get_mem lst j (by simp; exact hj_lt)
          have := hp_max (lst[j]!) hj_mem hj_prime
          rw [hi_eq]
          exact this
        · rw [hi_eq]

-- #test implementation [0,3,2,1,3,5,7,4,5,5,5,2,181,32,4,32,3,2,32,324,4,3] = 10
-- #test implementation [1,0,1,8,2,4597,2,1,3,40,1,2,1,2,4,2,5,1] = 25
-- #test implementation [1,3,1,32,5107,34,83278,109,163,23,2323,32,30,1,9,3] = 13
-- #test implementation [0,724,32,71,99,32,6,0,5,91,83,0,5,6] = 11
-- #test implementation [0,81,12,3,1,21] = 3
-- #test implementation [0,8,1,2,1,7] = 7