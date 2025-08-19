import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: String → String → Nat)
(string substring: String) :=
let spec (result: Nat) :=
(string.length < substring.length → result = 0)
∧
(string.length = substring.length →
((string = substring ↔ result = 1) ∧
(substring ≠ string ↔ result = 0)))
∧
(substring.length < string.length  →
let subtring_start_idx := {i: Nat | i ≤ string.length - substring.length};
let substring_occurrences := {i ∈ subtring_start_idx | (string.take (i + substring.length)).drop i = substring };
result = substring_occurrences.toFinset.card);
∃ result, implementation string substring = result ∧
spec result

-- LLM HELPER
def count_occurrences_aux (s : String) (sub : String) (start : Nat) : Nat :=
  if h : start + sub.length > s.length then 0
  else 
    let current_match := if (s.take (start + sub.length)).drop start = sub then 1 else 0
    current_match + count_occurrences_aux s sub (start + 1)
  termination_by s.length - start

def implementation (string: String) (substring: String) : Nat := 
  if substring.length = 0 then 0
  else if string.length < substring.length then 0
  else if string.length = substring.length then 
    if string = substring then 1 else 0
  else count_occurrences_aux string substring 0

-- LLM HELPER
lemma count_occurrences_aux_correct (s : String) (sub : String) (start : Nat) :
  start ≤ s.length - sub.length →
  count_occurrences_aux s sub start = 
  (Set.toFinite {i : Nat | start ≤ i ∧ i ≤ s.length - sub.length ∧ (s.take (i + sub.length)).drop i = sub}).toFinset.card := by
  intro h
  induction' Nat.sub_sub_self (le_of_lt (Nat.add_lt_of_pos_right (Nat.zero_lt_one))) with n ih
  · simp [count_occurrences_aux]
  · simp [count_occurrences_aux]
    split_ifs with h_over
    · simp
      apply Set.Finite.toFinset_card_eq_zero_iff.mpr
      intro i hi
      simp at hi
      omega
    · simp
      rw [ih]
      congr 1
      ext i
      simp
      constructor
      · intro ⟨h1, h2, h3⟩
        exact ⟨Nat.le_add_left _ _, h2, h3⟩
      · intro ⟨h1, h2, h3⟩
        cases' Nat.eq_or_lt_of_le h1 with h4 h4
        · exact ⟨h4, h2, h3⟩
        · exact ⟨Nat.le_of_succ_le_succ h4, h2, h3⟩
  · omega

-- LLM HELPER
lemma string_eq_iff_implementation_eq_one (s sub : String) :
  s.length = sub.length →
  (s = sub ↔ implementation s sub = 1) := by
  intro h
  constructor
  · intro eq
    simp [implementation, h, eq]
  · intro impl_eq
    simp [implementation, h] at impl_eq
    split_ifs at impl_eq with h_eq
    · exact h_eq
    · contradiction

theorem correctness
(string: String)
(substring: String)
: problem_spec implementation string substring := by
  use implementation string substring
  constructor
  · rfl
  · intro result h_eq
    rw [← h_eq]
    constructor
    · intro h_len
      simp [implementation, h_len]
    · constructor
      · intro h_len_eq
        constructor
        · constructor
          · intro h_str_eq
            simp [implementation, h_len_eq, h_str_eq]
          · intro h_impl_eq
            simp [implementation, h_len_eq] at h_impl_eq
            split_ifs at h_impl_eq with h_str_eq
            · exact h_str_eq
            · contradiction
        · constructor
          · intro h_str_ne
            simp [implementation, h_len_eq, h_str_ne]
          · intro h_impl_eq
            simp [implementation, h_len_eq] at h_impl_eq
            split_ifs at h_impl_eq with h_str_eq
            · contradiction
            · rfl
      · intro h_len_lt
        simp [implementation]
        split_ifs with h_sub_empty h_str_short h_str_eq
        · contradiction
        · contradiction
        · contradiction
        · apply count_occurrences_aux_correct
          omega