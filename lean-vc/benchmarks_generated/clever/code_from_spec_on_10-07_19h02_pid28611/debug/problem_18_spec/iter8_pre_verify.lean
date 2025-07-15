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
lemma count_occurrences_aux_eq_card (s sub: String) :
  count_occurrences_aux s sub 0 0 = 
  {i ∈ {i: Nat | i ≤ s.length - sub.length} | 
   (s.take (i + sub.length)).drop i = sub }.toFinset.card := by
  have h : Finite {i ∈ {i: Nat | i ≤ s.length - sub.length} | 
    (s.take (i + sub.length)).drop i = sub} := by
    apply Set.Finite.subset (Set.toFinite (Set.range (s.length + 1)))
    intro x hx
    simp at hx
    simp
    exact Nat.le_add_right x sub.length
  rw [Set.toFinset_card]
  -- This auxiliary function counts occurrences correctly
  have h_count : ∀ (pos acc : Nat), pos ≤ s.length - sub.length + 1 →
    count_occurrences_aux s sub pos acc = acc + 
    {i ∈ {i: Nat | pos ≤ i ∧ i ≤ s.length - sub.length} | 
     (s.take (i + sub.length)).drop i = sub }.toFinset.card := by
    intro pos acc h_pos
    induction pos, acc using count_occurrences_aux.induct
    case case1 pos acc h_term =>
      simp [count_occurrences_aux]
      split_ifs with h_over h_match
      · simp [Set.toFinset_card]
        congr 1
        ext i
        simp
        constructor
        · intro ⟨h_range, h_ge, h_le, h_eq⟩
          omega
        · intro h_contra
          omega
      · simp [Set.toFinset_card]
        have ih := h_term (by simp [h_over]) (by simp [h_match])
        rw [ih]
        congr 2
        ext i
        simp
        constructor
        · intro ⟨h_range, h_ge, h_le, h_eq⟩
          cases' Nat.eq_or_lt_of_le h_ge with h_eq_pos h_gt_pos
          · left
            constructor
            · exact h_eq_pos.symm ▸ h_eq
            · exact h_eq_pos.symm ▸ h_match
          · right
            exact ⟨h_range, h_gt_pos, h_le, h_eq⟩
        · intro h_or
          cases' h_or with h_pos h_rest
          · exact ⟨by simp, le_refl pos, by omega, h_pos.2⟩
          · exact ⟨h_rest.1, Nat.le_of_lt h_rest.2.1, h_rest.2.2.1, h_rest.2.2.2⟩
      · simp [Set.toFinset_card]
        have ih := h_term (by simp [h_over]) (by simp [h_match])
        rw [ih]
        congr 2
        ext i
        simp
        constructor
        · intro ⟨h_range, h_ge, h_le, h_eq⟩
          right
          exact ⟨h_range, Nat.lt_of_le_of_ne h_ge (Ne.symm (ne_of_not_eq (fun h_eq_pos => h_match (h_eq_pos ▸ h_eq)))), h_le, h_eq⟩
        · intro h_or
          cases' h_or with h_pos h_rest
          · exfalso
            exact h_match h_pos.2
          · exact ⟨h_rest.1, Nat.le_of_lt h_rest.2.1, h_rest.2.2.1, h_rest.2.2.2⟩
  have h_final := h_count 0 0 (by simp)
  rw [h_final]
  simp

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
            exact implementation_case2_ne string substring h h_ne.symm
          · intro h_imp
            by_contra h_eq
            have h_one := implementation_case2_eq string substring h h_eq.symm
            rw [h_one] at h_imp
            norm_num at h_imp
      · intro h
        rw [implementation_case3 string substring h]
        exact count_occurrences_aux_eq_card string substring