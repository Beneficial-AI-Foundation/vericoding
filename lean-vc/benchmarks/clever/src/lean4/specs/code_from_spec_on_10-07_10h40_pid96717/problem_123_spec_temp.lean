import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Nat → List Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: List Nat) :=
n > 0 →
result.Sorted (· < ·) ∧
∀ m, m ∈ result ↔ Odd m ∧ collatz_reachable n m -- m is reachable from starting point n
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def collatz_reachable (start target: Nat) : Prop :=
  ∃ k, collatz_iterate start k = target

-- LLM HELPER
def collatz_iterate (n: Nat) : Nat → Nat
  | 0 => n
  | k + 1 => collatz_step (collatz_iterate n k)

-- LLM HELPER
def collatz_step (n: Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

-- LLM HELPER
def collatz_sequence (n: Nat) (max_steps: Nat) : List Nat :=
  List.range max_steps |>.map (collatz_iterate n) |>.takeWhile (· != 1) ++ [1]

-- LLM HELPER
def filter_odd_sorted (l: List Nat) : List Nat :=
  l.filter Odd |>.toFinset.toList.sort (· < ·)

def implementation (n: Nat) : List Nat := 
  if n = 0 then [] else filter_odd_sorted (collatz_sequence n 1000)

-- LLM HELPER
lemma collatz_reachable_refl (n: Nat) : collatz_reachable n n := by
  use 0
  rfl

-- LLM HELPER  
lemma collatz_reachable_trans (a b c: Nat) : 
  collatz_reachable a b → collatz_reachable b c → collatz_reachable a c := by
  intro ⟨k1, h1⟩ ⟨k2, h2⟩
  use k1 + k2
  rw [← h2, ← h1]
  simp [collatz_iterate]
  
-- LLM HELPER
lemma collatz_step_reachable (n: Nat) : collatz_reachable n (collatz_step n) := by
  use 1
  simp [collatz_iterate]

-- LLM HELPER
lemma mem_collatz_sequence_iff (n m: Nat) (max_steps: Nat) :
  m ∈ collatz_sequence n max_steps ↔ (collatz_reachable n m ∧ (∃ k ≤ max_steps, collatz_iterate n k = m)) := by
  constructor
  · intro h
    constructor
    · simp [collatz_sequence] at h
      cases' h with h h
      · simp [List.mem_map] at h
        obtain ⟨k, hk1, hk2⟩ := h
        use k
        exact hk2.symm
      · simp at h
        subst h
        use max_steps
        simp [collatz_iterate]
    · simp [collatz_sequence] at h
      cases' h with h h
      · simp [List.mem_map] at h
        obtain ⟨k, hk1, hk2⟩ := h
        use k
        simp [List.mem_range] at hk1
        exact ⟨hk1, hk2.symm⟩
      · simp at h
        subst h
        use max_steps
        simp
  · intro ⟨_, ⟨k, hk1, hk2⟩⟩
    simp [collatz_sequence]
    if h : k < max_steps then
      left
      simp [List.mem_map]
      use k
      exact ⟨List.mem_range.mpr h, hk2.symm⟩
    else
      right
      simp
      cases' Nat.lt_or_eq_of_le (Nat.le_of_not_gt h) with h' h'
      · exfalso
        exact h h'
      · subst h'
        exact hk2.symm

-- LLM HELPER
lemma sorted_filter_odd_sorted (l: List Nat) : (filter_odd_sorted l).Sorted (· < ·) := by
  simp [filter_odd_sorted]
  apply List.sorted_sort

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · intro h
    simp [implementation]
    rw [if_pos h]
    constructor
    · exact sorted_filter_odd_sorted (collatz_sequence n 1000)
    · intro m
      simp [filter_odd_sorted]
      constructor
      · intro h_mem
        simp [List.mem_sort] at h_mem
        simp [List.mem_toList] at h_mem
        simp [List.mem_toFinset] at h_mem
        simp [List.mem_filter] at h_mem
        exact ⟨h_mem.2, h_mem.1⟩
      · intro ⟨h_odd, h_reach⟩
        simp [List.mem_sort]
        simp [List.mem_toList]
        simp [List.mem_toFinset]
        simp [List.mem_filter]
        exact ⟨h_reach, h_odd⟩