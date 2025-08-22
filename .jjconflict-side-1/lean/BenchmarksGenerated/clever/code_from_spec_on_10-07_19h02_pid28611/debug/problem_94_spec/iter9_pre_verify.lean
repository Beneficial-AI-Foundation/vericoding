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
def sumOfDigits (n: Nat) : Nat :=
  (Nat.digits 10 n).sum

def implementation (lst: List Nat) : Nat :=
  let primes := lst.filter Nat.Prime
  if primes.isEmpty then 0
  else
    let minPrime := primes.min?
    match minPrime with
    | none => 0
    | some p => sumOfDigits p

-- LLM HELPER
lemma list_any_filter_equiv (lst: List Nat) :
  lst.any (fun num => Nat.Prime num) ↔ ¬(lst.filter Nat.Prime).isEmpty := by
  simp [List.any_eq_true, List.isEmpty_iff]
  constructor
  · intro h
    obtain ⟨x, hx_mem, hx_prime⟩ := h
    exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hx_mem, hx_prime⟩)
  · intro h
    rw [← List.ne_nil_iff_exists_mem] at h
    obtain ⟨x, hx_mem⟩ := h
    rw [List.mem_filter] at hx_mem
    exact ⟨x, hx_mem.1, hx_mem.2⟩

-- LLM HELPER
lemma filter_minimum_in_original (lst: List Nat) (primes: List Nat) (min_prime: Nat) :
  primes = lst.filter Nat.Prime →
  primes.min? = some min_prime →
  ∃ i, i < lst.length ∧ lst.get! i = min_prime := by
  intro h_eq h_min
  have h_mem : min_prime ∈ primes := by
    rw [List.min?_eq_some_iff] at h_min
    exact h_min.1
  rw [h_eq] at h_mem
  rw [List.mem_filter] at h_mem
  obtain ⟨h_mem_orig, _⟩ := h_mem
  have : ∃ n : Fin lst.length, lst.get n = min_prime := List.mem_iff_get.mp h_mem_orig
  obtain ⟨n, hn⟩ := this
  use n.val
  constructor
  · exact n.isLt
  · rw [← hn]
    rw [List.get!_pos]
    exact n.isLt

-- LLM HELPER
lemma minimum_is_smallest (lst: List Nat) (min_val: Nat) :
  lst.min? = some min_val → ∀ x ∈ lst, min_val ≤ x := by
  intro h_min x h_mem
  rw [List.min?_eq_some_iff] at h_min
  exact h_min.2 x h_mem

-- LLM HELPER
lemma digits_sum_pos_of_prime (p: Nat) : Nat.Prime p → (Nat.digits 10 p).sum > 0 := by
  intro h_prime
  have h_pos : p > 0 := Nat.Prime.pos h_prime
  have h_ne_zero : p ≠ 0 := ne_of_gt h_pos
  rw [Nat.sum_digits_pos_iff']
  exact h_ne_zero

-- LLM HELPER
lemma min_some_of_nonempty (lst: List Nat) : 
  ¬lst.isEmpty → ∃ m, lst.min? = some m := by
  intro h
  rw [List.isEmpty_iff] at h
  have : lst ≠ [] := h
  simp [← List.ne_nil_iff_exists_mem] at this
  obtain ⟨x, hx⟩ := this
  use lst.min' ⟨x, hx⟩
  rw [List.min?_eq_some_iff]
  constructor
  · exact List.min'_mem _ _
  · intro y hy
    exact List.min'_le _ y hy

-- LLM HELPER
lemma get_mem_of_lt (lst: List Nat) (i: Nat) : i < lst.length → lst.get! i ∈ lst := by
  intro h
  exact List.get!_mem lst i h

theorem correctness
(lst: List Nat)
: problem_spec implementation lst := by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · unfold implementation
    let primes := lst.filter Nat.Prime
    by_cases h : primes.isEmpty
    · simp [h]
      intro h_any
      rw [list_any_filter_equiv] at h_any
      exact h_any h
    · simp [h]
      obtain ⟨min_prime, h_min⟩ := min_some_of_nonempty primes h
      simp [h_min]
      intro h_any
      constructor
      · have h_mem : min_prime ∈ primes := by
          rw [List.min?_eq_some_iff] at h_min
          exact h_min.1
        rw [List.mem_filter] at h_mem
        exact digits_sum_pos_of_prime min_prime h_mem.2
      · obtain ⟨i, hi_lt, hi_eq⟩ := filter_minimum_in_original lst primes min_prime rfl h_min
        use i
        constructor
        · exact hi_lt
        · constructor
          · rw [hi_eq]
            have h_mem : min_prime ∈ primes := by
              rw [List.min?_eq_some_iff] at h_min
              exact h_min.1
            rw [List.mem_filter] at h_mem
            exact h_mem.2
          · constructor
            · intro j ⟨hj_lt, hj_prime⟩
              have hj_mem : lst.get! j ∈ primes := by
                rw [List.mem_filter]
                exact ⟨get_mem_of_lt lst j hj_lt, hj_prime⟩
              rw [← hi_eq]
              exact minimum_is_smallest primes min_prime h_min (lst.get! j) hj_mem
            · rw [hi_eq]
              rfl