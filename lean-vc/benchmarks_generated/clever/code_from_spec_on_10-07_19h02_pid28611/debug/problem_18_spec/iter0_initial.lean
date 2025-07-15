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
def count_occurrences_aux (s sub: String) (pos: Nat) (acc: Nat) : Nat :=
if pos + sub.length > s.length then acc
else if (s.take (pos + sub.length)).drop pos = sub then
  count_occurrences_aux s sub (pos + 1) (acc + 1)
else
  count_occurrences_aux s sub (pos + 1) acc

def implementation (string: String) (substring: String) : Nat := 
if string.length < substring.length then 0
else if string.length = substring.length then
  if string = substring then 1 else 0
else
  count_occurrences_aux string substring 0 0

-- LLM HELPER
lemma count_occurrences_aux_correct (s sub: String) (pos acc: Nat) :
  pos ≤ s.length - sub.length + 1 →
  count_occurrences_aux s sub pos acc = acc + 
    (Finset.filter (fun i => (s.take (i + sub.length)).drop i = sub) 
      (Finset.range (s.length - sub.length + 1 - pos))).card :=
by
  sorry

-- LLM HELPER
lemma implementation_case1 (string substring: String) :
  string.length < substring.length →
  implementation string substring = 0 :=
by
  intro h
  simp [implementation]
  rw [if_pos h]

-- LLM HELPER
lemma implementation_case2 (string substring: String) :
  string.length = substring.length →
  implementation string substring = (if string = substring then 1 else 0) :=
by
  intro h
  simp [implementation]
  rw [if_neg (not_lt.mpr (le_of_eq h)), if_pos h]

-- LLM HELPER
lemma implementation_case3 (string substring: String) :
  substring.length < string.length →
  implementation string substring = count_occurrences_aux string substring 0 0 :=
by
  intro h
  simp [implementation]
  rw [if_neg (not_lt.mpr (le_of_lt h)), if_neg (ne_of_gt h)]

theorem correctness
(string: String)
(substring: String)
: problem_spec implementation string substring := by
  use implementation string substring
  constructor
  · rfl
  · constructor
    · intro h
      exact implementation_case1 string substring h
    · constructor
      · intro h
        constructor
        · intro h_eq
          rw [implementation_case2 string substring h, if_pos h_eq]
        · intro h_ne
          rw [implementation_case2 string substring h, if_neg h_ne]
      · intro h
        sorry