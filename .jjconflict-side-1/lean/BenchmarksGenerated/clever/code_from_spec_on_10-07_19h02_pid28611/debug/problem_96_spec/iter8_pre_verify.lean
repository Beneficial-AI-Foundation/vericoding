import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → List Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result : List Nat) :=
  match n with
  | 0 => result = []
  | n => n > 0 → (∀ i, i < result.length → (Nat.Prime (result.get! i)) ∧ (result.get! i) < n) ∧
         (∀ i : Nat, i < n → Nat.Prime i → i ∈ result)
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
def range_from (start: Nat) (n: Nat) : List Nat :=
  if start >= n then []
  else start :: range_from (start + 1) n
termination_by n - start

def implementation (n: Nat) : List Nat := 
  match n with
  | 0 => []
  | n => (range_from 2 n).filter Nat.Prime

-- LLM HELPER
lemma range_from_mem (start n k : Nat) : k ∈ range_from start n ↔ start ≤ k ∧ k < n := by
  revert start
  induction n with
  | zero => 
    intro start
    simp [range_from]
    constructor
    · intro h
      cases h
    · intro ⟨_, h_lt⟩
      cases h_lt
  | succ n ih =>
    intro start
    simp [range_from]
    cases' Nat.lt_or_ge start (n + 1) with h h
    · simp [if_neg (Nat.not_le.mpr h)]
      rw [ih]
      constructor
      · intro h_mem
        cases' h_mem with h_eq h_in
        · simp [h_eq]
          exact ⟨Nat.le_refl _, h⟩
        · exact ⟨Nat.le_succ_of_le h_in.1, Nat.lt_succ_of_le h_in.2⟩
      · intro ⟨h_ge, h_lt⟩
        cases' Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h_lt) with h_eq h_lt'
        · left
          exact h_eq.symm
        · right
          exact ⟨Nat.succ_le_iff.mp h_ge, h_lt'⟩
    · simp [if_pos h]
      constructor
      · intro h_mem
        cases h_mem
      · intro ⟨h_ge, h_lt⟩
        exfalso
        exact Nat.not_le.mpr h_lt h

-- LLM HELPER
lemma range_from_all_ge (start n : Nat) : ∀ k ∈ range_from start n, start ≤ k := by
  intros k h_mem
  rw [range_from_mem] at h_mem
  exact h_mem.1

-- LLM HELPER  
lemma range_from_all_lt (start n : Nat) : ∀ k ∈ range_from start n, k < n := by
  intros k h_mem
  rw [range_from_mem] at h_mem
  exact h_mem.2

-- LLM HELPER
lemma filter_prime_all_prime (l : List Nat) : ∀ p ∈ l.filter Nat.Prime, Nat.Prime p := by
  intros p h_mem
  rw [List.mem_filter] at h_mem
  exact h_mem.2

-- LLM HELPER
lemma filter_prime_mem_original (l : List Nat) : ∀ p ∈ l.filter Nat.Prime, p ∈ l := by
  intros p h_mem
  rw [List.mem_filter] at h_mem
  exact h_mem.1

-- LLM HELPER
lemma prime_in_range_in_filter (l : List Nat) (p : Nat) : p ∈ l → Nat.Prime p → p ∈ l.filter Nat.Prime := by
  intros h_mem h_prime
  rw [List.mem_filter]
  exact ⟨h_mem, h_prime⟩

-- LLM HELPER
lemma get_mem_of_lt_length (l : List Nat) (i : Nat) (h : i < l.length) : l.get! i ∈ l := by
  exact List.get!_mem _ _ h

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · simp [implementation]
    cases n with
    | zero => rfl
    | succ n =>
      intro h_pos
      constructor
      · intros i h_i
        have h_mem : (range_from 2 (n + 1)).filter Nat.Prime |>.get! i ∈ (range_from 2 (n + 1)).filter Nat.Prime := by
          apply get_mem_of_lt_length
          exact h_i
        constructor
        · exact filter_prime_all_prime _ _ h_mem
        · have h_orig : (range_from 2 (n + 1)).filter Nat.Prime |>.get! i ∈ range_from 2 (n + 1) := 
            filter_prime_mem_original _ _ h_mem
          have h_lt := range_from_all_lt 2 (n + 1) _ h_orig
          exact h_lt
      · intros i h_i h_prime
        have h_ge : 2 ≤ i := Nat.Prime.two_le h_prime
        have h_in_range : i ∈ range_from 2 (n + 1) := by
          rw [range_from_mem]
          exact ⟨h_ge, h_i⟩
        exact prime_in_range_in_filter _ _ h_in_range h_prime