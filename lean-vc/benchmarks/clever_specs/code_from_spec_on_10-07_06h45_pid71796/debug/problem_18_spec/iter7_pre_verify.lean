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
let substring_occurrences := {i ∈ subtring_start_idx | (string.take (i + substring.length)).drop i = substring}
result = substring_occurrences.toFinset.card)
∃ result, implementation string substring = result ∧
spec result

-- LLM HELPER
def String.substr (s : String) (start : Nat) (len : Nat) : String :=
  (s.toList.drop start).take len |>.asString

-- LLM HELPER
def countSubstringOccurrences (s : String) (sub : String) : Nat :=
  if sub.length = 0 then 0
  else if s.length < sub.length then 0
  else 
    let rec countAt (pos : Nat) (acc : Nat) : Nat :=
      if pos > s.length - sub.length then acc
      else 
        let current_match := s.substr pos sub.length = sub
        countAt (pos + 1) (if current_match then acc + 1 else acc)
    termination_by s.length - pos
    decreasing_by simp_wf; sorry
    countAt 0 0

def implementation (string: String) (substring: String) : Nat := 
  if substring.length = 0 then 0
  else if string.length < substring.length then 0
  else if string.length = substring.length then 
    if string = substring then 1 else 0
  else countSubstringOccurrences string substring

-- LLM HELPER
lemma String.substr_eq_take_drop (s : String) (start len : Nat) :
  s.substr start len = (s.take (start + len)).drop start := by
  simp [String.substr]
  rw [String.asString_toList]
  simp [String.take, String.drop]
  congr 1
  rw [List.take_drop]

-- LLM HELPER
lemma countSubstringOccurrences_correct (s : String) (sub : String) 
  (h : sub.length < s.length) :
  let subtring_start_idx := {i: Nat | i ≤ s.length - sub.length}
  let substring_occurrences := {i ∈ subtring_start_idx | (s.take (i + sub.length)).drop i = sub}
  countSubstringOccurrences s sub = substring_occurrences.toFinset.card := by
  simp [countSubstringOccurrences]
  split_ifs with h1 h2
  · contradiction
  · contradiction  
  · sorry

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
      simp [countSubstringOccurrences, h]
    · constructor
      · intro h
        constructor
        · intro h_eq
          simp [h, h_eq]
        · intro h_neq
          simp [h, h_neq]
      · intro h
        exact countSubstringOccurrences_correct string substring h