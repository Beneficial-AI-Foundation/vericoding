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
termination_by (s.length - pos)
decreasing_by
  simp_wf
  cases' h : pos + sub.length > s.length with
  · simp [h]
    omega
  · simp [h]
    omega

def implementation (string: String) (substring: String) : Nat := 
if string.length < substring.length then 0
else if string.length = substring.length then
  if string = substring then 1 else 0
else
  count_occurrences_aux string substring 0 0

-- LLM HELPER  
lemma count_occurrences_aux_spec (s sub: String) (pos acc: Nat) :
  pos ≤ s.length - sub.length + 1 →
  count_occurrences_aux s sub pos acc = acc + 
    (Finset.filter (fun i => pos ≤ i ∧ i ≤ s.length - sub.length ∧ (s.take (i + sub.length)).drop i = sub) 
      (Finset.range (s.length + 1))).card :=
by
  intro h
  have : count_occurrences_aux s sub pos acc = 
    {i ∈ {i: Nat | i ≤ s.length - sub.length} | 
     (s.take (i + sub.length)).drop i = sub }.toFinset.card := by
    simp [count_occurrences_aux]
    rfl
  exact this

-- LLM HELPER
lemma implementation_case1 (string substring: String) :
  string.length < substring.length →
  implementation string substring = 0 :=
by
  intro h
  simp [implementation, h]

-- LLM HELPER
lemma implementation_case2_eq (string substring: String) :
  string.length = substring.length →
  string = substring →
  implementation string substring = 1 :=
by
  intro h_len h_eq
  simp [implementation]
  have : ¬string.length < substring.length := by omega
  simp [this, h_len, h_eq]

-- LLM HELPER
lemma implementation_case2_ne (string substring: String) :
  string.length = substring.length →
  string ≠ substring →
  implementation string substring = 0 :=
by
  intro h_len h_ne
  simp [implementation]
  have : ¬string.length < substring.length := by omega
  simp [this, h_len, h_ne]

-- LLM HELPER
lemma implementation_case3 (string substring: String) :
  substring.length < string.length →
  implementation string substring = count_occurrences_aux string substring 0 0 :=
by
  intro h
  simp [implementation]
  have h1 : ¬string.length < substring.length := by omega
  have h2 : ¬string.length = substring.length := by omega
  simp [h1, h2]

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
        · constructor
          · intro h_eq
            exact implementation_case2_eq string substring h h_eq
          · intro h_imp
            have h_eq : string = substring := by
              by_contra h_ne
              have h_zero := implementation_case2_ne string substring h h_ne
              rw [h_zero] at h_imp
              norm_num at h_imp
            exact h_eq
        · constructor
          · intro h_ne
            exact implementation_case2_ne string substring h h_ne
          · intro h_imp
            by_contra h_eq
            have h_one := implementation_case2_eq string substring h h_eq
            rw [h_one] at h_imp
            norm_num at h_imp
      · intro h
        rw [implementation_case3 string substring h]
        have h_card : count_occurrences_aux string substring 0 0 = 
          {i ∈ {i: Nat | i ≤ string.length - substring.length} | 
           (string.take (i + substring.length)).drop i = substring }.toFinset.card := by
          simp [count_occurrences_aux]
          rfl
        exact h_card