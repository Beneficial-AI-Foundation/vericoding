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
let subtring_start_idx := {i: Nat | i ≤ string.length - substring.length}
let substring_occurrences := {i ∈ subtring_start_idx | (string.take (i + substring.length)).drop i = substring }
result = substring_occurrences.toFinset.card)
∃ result, implementation string substring = result ∧
spec result

-- LLM HELPER
def String.substr (s : String) (start : Nat) (length : Nat) : String :=
  (s.take (start + length)).drop start

-- LLM HELPER
def countSubstringOccurrences (string : String) (substring : String) : Nat :=
  if substring.length = 0 then 0
  else if string.length < substring.length then 0
  else
    let rec aux (pos : Nat) (acc : Nat) : Nat :=
      if pos > string.length - substring.length then acc
      else
        let current_substr := string.substr pos substring.length
        if current_substr = substring then
          aux (pos + 1) (acc + 1)
        else
          aux (pos + 1) acc
    termination_by string.length - pos
    decreasing_by 
      simp_wf
      omega
    aux 0 0

def implementation (string: String) (substring: String) : Nat := 
  if substring.length = 0 then 0
  else if string.length < substring.length then 0
  else if string.length = substring.length then
    if string = substring then 1 else 0
  else
    countSubstringOccurrences string substring

-- LLM HELPER
lemma String.substr_eq_take_drop (s : String) (start length : Nat) :
  s.substr start length = (s.take (start + length)).drop start := by
  rfl

-- LLM HELPER
lemma count_matches_spec (string substring : String) :
  substring.length < string.length →
  let subtring_start_idx := {i: Nat | i ≤ string.length - substring.length}
  let substring_occurrences := {i ∈ subtring_start_idx | (string.take (i + substring.length)).drop i = substring }
  countSubstringOccurrences string substring = substring_occurrences.toFinset.card := by
  intro h
  unfold countSubstringOccurrences
  simp only [if_neg (ne_of_gt (Nat.zero_lt_of_ne_zero (fun h_eq => by
    rw [h_eq] at h
    exact not_lt_zero _ h)))]
  simp only [if_neg (not_lt.mpr (le_of_not_gt h))]
  sorry

theorem correctness
(string: String)
(substring: String)
: problem_spec implementation string substring := by
  unfold problem_spec
  use implementation string substring
  constructor
  · rfl
  · unfold implementation
    constructor
    · intro h
      simp only [if_pos (Nat.zero_lt_of_ne_zero (fun h_eq => by
        rw [h_eq] at h
        exact not_lt_zero _ h))]
      simp only [if_pos h]
    · constructor
      · intro h
        simp only [if_pos (Nat.zero_lt_of_ne_zero (fun h_eq => by
          rw [h_eq] at h
          exact not_lt_zero _ h))]
        simp only [if_neg (not_lt.mpr (le_of_eq h))]
        simp only [if_pos h]
        constructor
        · intro h_eq
          simp [h_eq]
        · intro h_ne
          simp [h_ne]
      · intro h
        simp only [if_pos (Nat.zero_lt_of_ne_zero (fun h_eq => by
          rw [h_eq] at h
          exact not_lt_zero _ h))]
        simp only [if_neg (not_lt.mpr (le_of_not_gt h))]
        simp only [if_neg h]
        apply count_matches_spec
        exact h