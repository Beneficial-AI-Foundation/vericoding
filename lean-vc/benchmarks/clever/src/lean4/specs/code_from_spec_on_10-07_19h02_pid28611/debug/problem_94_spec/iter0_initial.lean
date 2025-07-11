import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Nat → Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : Nat) :=
  lst.any (fun num => Nat.Prime num) →
    result > 0 ∧ ∃ i, i < lst.length ∧ Prime (lst.get! i) ∧
    (∀ j, j < lst.length ∧ Prime (lst.get! j) → lst.get! i ≤ lst.get! j) ∧
    result = (Nat.digits 10 (lst.get! i)).sum
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def findMinPrime (lst: List Nat) : Option Nat :=
  let primes := lst.filter Nat.Prime
  if primes.isEmpty then none else some (primes.minimum?)

-- LLM HELPER
def sumOfDigits (n: Nat) : Nat :=
  (Nat.digits 10 n).sum

def implementation (lst: List Nat) : Nat :=
  let primes := lst.filter Nat.Prime
  if primes.isEmpty then 0
  else
    let minPrime := primes.minimum?
    match minPrime with
    | none => 0
    | some p => sumOfDigits p

-- LLM HELPER
lemma list_any_filter_equiv (lst: List Nat) :
  lst.any (fun num => Nat.Prime num) ↔ ¬(lst.filter Nat.Prime).isEmpty := by
  simp [List.any_eq_true, List.isEmpty_iff_eq_nil]
  constructor
  · intro h
    obtain ⟨x, hx_mem, hx_prime⟩ := h
    exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hx_mem, hx_prime⟩)
  · intro h
    rw [List.ne_nil_iff_exists_mem] at h
    obtain ⟨x, hx_mem⟩ := h
    rw [List.mem_filter] at hx_mem
    exact ⟨x, hx_mem.1, hx_mem.2⟩

-- LLM HELPER
lemma filter_minimum_in_original (lst: List Nat) (primes: List Nat) (min_prime: Nat) :
  primes = lst.filter Nat.Prime →
  primes.minimum? = min_prime →
  ∃ i, i < lst.length ∧ lst.get! i = min_prime := by
  intro h_eq h_min
  have h_mem : min_prime ∈ primes := by
    rw [← h_min]
    exact List.minimum?_mem (List.ne_nil_of_minimum?_eq_some h_min)
  rw [h_eq] at h_mem
  rw [List.mem_filter] at h_mem
  obtain ⟨h_mem_orig, _⟩ := h_mem
  exact List.mem_iff_get.mp h_mem_orig

-- LLM HELPER
lemma minimum_is_smallest (lst: List Nat) (min_val: Nat) :
  lst.minimum? = min_val → ∀ x ∈ lst, min_val ≤ x := by
  intro h_min x h_mem
  rw [← h_min]
  exact List.minimum?_le_of_mem h_mem (List.ne_nil_of_minimum?_eq_some h_min)

-- LLM HELPER
lemma digits_sum_pos_of_prime (p: Nat) : Prime p → (Nat.digits 10 p).sum > 0 := by
  intro h_prime
  have h_pos : p > 0 := Prime.pos h_prime
  have h_ge_2 : p ≥ 2 := Prime.two_le h_prime
  cases' p with p
  · exact absurd h_pos (Nat.not_lt_zero 0)
  · simp [Nat.digits_sum_pos_iff]
    exact Nat.succ_pos p

theorem correctness
(lst: List Nat)
: problem_spec implementation lst := by
  unfold problem_spec
  simp [implementation]
  let primes := lst.filter Nat.Prime
  by_cases h : primes.isEmpty
  · simp [h]
    intro h_any
    rw [list_any_filter_equiv] at h_any
    exact absurd h_any (not_not.mpr h)
  · simp [h]
    obtain ⟨min_prime, h_min⟩ := List.minimum?_of_not_isEmpty h
    simp [h_min]
    intro h_any
    constructor
    · exact digits_sum_pos_of_prime min_prime (by
        have h_mem : min_prime ∈ primes := List.minimum?_mem (List.ne_nil_of_minimum?_eq_some h_min)
        rw [List.mem_filter] at h_mem
        exact h_mem.2)
    · obtain ⟨i, hi_lt, hi_eq⟩ := filter_minimum_in_original lst primes min_prime rfl h_min
      use i
      constructor
      · exact hi_lt
      · constructor
        · rw [hi_eq]
          have h_mem : min_prime ∈ primes := List.minimum?_mem (List.ne_nil_of_minimum?_eq_some h_min)
          rw [List.mem_filter] at h_mem
          exact h_mem.2
        · constructor
          · intro j hj_lt hj_prime
            have hj_mem : lst.get! j ∈ primes := by
              rw [List.mem_filter]
              exact ⟨List.get!_mem lst j hj_lt, hj_prime⟩
            rw [← hi_eq]
            exact minimum_is_smallest primes min_prime h_min (lst.get! j) hj_mem
          · rw [hi_eq]
            rfl