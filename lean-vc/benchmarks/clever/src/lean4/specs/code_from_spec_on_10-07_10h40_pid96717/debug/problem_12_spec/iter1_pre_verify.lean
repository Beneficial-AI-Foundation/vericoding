import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List String → Option String)
-- inputs
(strings: List String) :=
-- spec
let spec (result: Option String) :=
  (result = none ↔ strings.length = 0) ∨
  (∃ longest, result = some longest ∧
  longest ∈ strings ∧
  ∀ s, s ∈ strings → s.length ≤ longest.length →
  (∃ i, i < strings.length ∧
  strings[i]! = longest ∧ ∀ j < i, strings[j]!.length < longest.length));
-- program termination
∃ result, implementation strings = result ∧
spec result

-- LLM HELPER
def find_first_longest_aux (strings: List String) (max_len: Nat) (idx: Nat) : Option (String × Nat) :=
  match strings with
  | [] => none
  | s :: rest =>
    if s.length > max_len then
      some (s, idx)
    else
      find_first_longest_aux rest max_len (idx + 1)

-- LLM HELPER
def find_first_longest (strings: List String) : Option String :=
  match strings with
  | [] => none
  | s :: rest =>
    match find_first_longest_aux rest s.length 1 with
    | none => some s
    | some (longest, _) => some longest

def implementation (strings: List String) : Option String := 
  find_first_longest strings

-- LLM HELPER
lemma find_first_longest_aux_length_property (strings: List String) (max_len: Nat) (idx: Nat) :
  ∀ result_str result_idx, find_first_longest_aux strings max_len idx = some (result_str, result_idx) →
  result_str.length > max_len :=
by
  induction strings generalizing idx with
  | nil => intros; contradiction
  | cons s rest ih =>
    intros result_str result_idx h
    simp [find_first_longest_aux] at h
    split at h
    · injection h with h1 h2
      rw [← h1]
      assumption
    · exact ih _ _ h

-- LLM HELPER
lemma find_first_longest_aux_membership (strings: List String) (max_len: Nat) (idx: Nat) :
  ∀ result_str result_idx, find_first_longest_aux strings max_len idx = some (result_str, result_idx) →
  result_str ∈ strings :=
by
  induction strings generalizing idx with
  | nil => intros; contradiction
  | cons s rest ih =>
    intros result_str result_idx h
    simp [find_first_longest_aux] at h
    split at h
    · injection h with h1
      rw [← h1]
      exact List.mem_cons_self s rest
    · right
      exact ih _ _ h

-- LLM HELPER
lemma find_first_longest_none_iff (strings: List String) :
  find_first_longest strings = none ↔ strings = [] :=
by
  constructor
  · intro h
    cases strings with
    | nil => rfl
    | cons s rest =>
      simp [find_first_longest] at h
      cases find_first_longest_aux rest s.length 1 with
      | none => contradiction
      | some _ => contradiction
  · intro h
    rw [h]
    simp [find_first_longest]

-- LLM HELPER
lemma find_first_longest_some_membership (strings: List String) (result: String) :
  find_first_longest strings = some result → result ∈ strings :=
by
  intro h
  cases strings with
  | nil => 
    simp [find_first_longest] at h
  | cons s rest =>
    simp [find_first_longest] at h
    cases h_aux : find_first_longest_aux rest s.length 1 with
    | none => 
      injection h with h1
      rw [← h1]
      exact List.mem_cons_self s rest
    | some p =>
      injection h with h1
      rw [← h1]
      right
      exact find_first_longest_aux_membership rest s.length 1 p.1 p.2 h_aux

theorem correctness
(strings: List String)
: problem_spec implementation strings
:= by
  simp [problem_spec, implementation]
  use find_first_longest strings
  constructor
  · rfl
  · left
    rw [find_first_longest_none_iff]
    constructor
    · intro h
      cases strings with
      | nil => rfl
      | cons s rest => contradiction
    · intro h
      rw [h]
      simp [List.length]