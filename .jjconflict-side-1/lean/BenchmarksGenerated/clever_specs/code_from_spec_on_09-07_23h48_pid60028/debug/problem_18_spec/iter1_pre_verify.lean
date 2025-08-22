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
  sorry

theorem correctness
(string: String)
(substring: String)
: problem_spec implementation string substring := by
  unfold problem_spec implementation
  simp only [countSubstringOccurrences]
  split_ifs with h1 h2 h3
  · -- Case: substring.length = 0
    use 0
    constructor
    · rfl
    · constructor
      · intro h
        simp at h
        rfl
      constructor
      · intro h
        simp at h
        cases h with
        | inl h => contradiction
        | inr h => simp [h]
      · intro h
        simp at h
        cases h with
        | inl h => contradiction
        | inr h => simp [h]
  · -- Case: string.length < substring.length
    use 0
    constructor
    · rfl
    · constructor
      · intro h
        exact h2
      constructor
      · intro h
        simp at h
        exact absurd h2 (not_lt.mpr h)
      · intro h
        simp at h
        exact absurd h2 (not_lt.mpr h)
  · -- Case: string.length = substring.length
    split_ifs with h4
    · -- string = substring
      use 1
      constructor
      · rfl
      · constructor
        · intro h
          exact absurd h2 (not_lt.mpr (le_of_eq h3))
        constructor
        · intro h
          simp at h
          exact absurd h2 (not_lt.mpr (le_of_eq h3))
        · intro h
          simp at h
          exact absurd h2 (not_lt.mpr (le_of_eq h3))
    · -- string ≠ substring
      use 0
      constructor
      · rfl
      · constructor
        · intro h
          exact absurd h2 (not_lt.mpr (le_of_eq h3))
        constructor
        · intro h
          simp at h
          exact absurd h2 (not_lt.mpr (le_of_eq h3))
        · intro h
          simp at h
          exact absurd h2 (not_lt.mpr (le_of_eq h3))
  · -- Case: substring.length < string.length
    use countSubstringOccurrences string substring
    constructor
    · rfl
    · constructor
      · intro h
        exact absurd h (not_lt.mpr (le_of_not_gt h2))
      constructor
      · intro h
        exact absurd h3 h
      · intro h
        apply count_matches_spec
        exact h