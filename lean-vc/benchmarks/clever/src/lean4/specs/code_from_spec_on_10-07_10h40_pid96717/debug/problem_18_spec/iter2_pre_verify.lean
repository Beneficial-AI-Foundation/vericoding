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
def string_slice (s: String) (start: Nat) (len: Nat) : String :=
  (s.drop start).take len

-- LLM HELPER
def count_occurrences_aux (string: String) (substring: String) (start: Nat) (acc: Nat) : Nat :=
  if start + substring.length > string.length then acc
  else if string_slice string start substring.length = substring then
    count_occurrences_aux string substring (start + 1) (acc + 1)
  else
    count_occurrences_aux string substring (start + 1) acc

def implementation (string: String) (substring: String) : Nat := 
  if string.length < substring.length then 0
  else if string.length = substring.length then
    if string = substring then 1 else 0
  else
    count_occurrences_aux string substring 0 0

-- LLM HELPER
lemma string_slice_eq_take_drop (s: String) (start: Nat) (len: Nat) :
  string_slice s start len = (s.drop start).take len := by
  rfl

-- LLM HELPER
lemma string_slice_correct (s: String) (start len: Nat) :
  start + len ≤ s.length → string_slice s start len = (s.take (start + len)).drop start := by
  intro h
  rw [string_slice_eq_take_drop]
  rw [String.take_drop]

-- LLM HELPER
lemma count_occurrences_aux_correct (string substring: String) (start acc: Nat) :
  start ≤ string.length - substring.length + 1 →
  count_occurrences_aux string substring start acc = 
  acc + (({i | start ≤ i ∧ i ≤ string.length - substring.length ∧ string_slice string i substring.length = substring} : Set Nat).ncard) := by
  intro h
  induction start, string.length - substring.length + 1 - start using Nat.strong_induction_on with
  | ind n ih =>
    unfold count_occurrences_aux
    split_ifs with h1 h2
    · simp [Set.ncard_eq_zero]
      ext i
      simp
      intro h_start h_bound h_eq
      omega
    · simp [string_slice_correct]
      rw [ih]
      simp [Set.ncard_eq_succ_iff]
      omega
      omega
    · rw [ih]
      simp [Set.ncard_eq_zero]
      omega
      omega

theorem correctness
(string: String)
(substring: String)
: problem_spec implementation string substring := by
  unfold problem_spec
  use implementation string substring
  constructor
  · rfl
  · unfold implementation
    simp only [and_true]
    constructor
    · intro h
      simp [h]
    · constructor
      · intro h
        simp [h]
        constructor
        · intro h_eq
          simp [h_eq]
        · intro h_ne
          simp [h_ne]
      · intro h
        simp [h]
        have h_aux : count_occurrences_aux string substring 0 0 = 
          (({i | 0 ≤ i ∧ i ≤ string.length - substring.length ∧ string_slice string i substring.length = substring} : Set Nat).ncard) := by
          apply count_occurrences_aux_correct
          omega
        rw [h_aux]
        simp [Set.ncard_eq_toFinset_card]
        congr 1
        ext i
        simp
        constructor
        · intro h_bound h_eq
          constructor
          · omega
          · rw [string_slice_correct] at h_eq
            exact h_eq
            omega
        · intro h_bound h_eq
          constructor
          · omega
          · rw [string_slice_correct]
            exact h_eq
            omega