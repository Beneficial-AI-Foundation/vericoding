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
def find_longest_aux (strings: List String) (idx: Nat) (best_idx: Nat) (best_len: Nat) : Nat :=
  match strings.get? idx with
  | none => best_idx
  | some s => 
    if s.length > best_len then
      find_longest_aux strings (idx + 1) idx s.length
    else
      find_longest_aux strings (idx + 1) best_idx best_len

def implementation (strings: List String) : Option String :=
  match strings with
  | [] => none
  | h :: _ => 
    let best_idx := find_longest_aux strings 0 0 h.length
    some (strings[best_idx]!)

-- LLM HELPER
lemma find_longest_aux_valid (strings: List String) (idx best_idx: Nat) (best_len: Nat) :
  best_idx < strings.length →
  idx ≤ strings.length →
  find_longest_aux strings idx best_idx best_len < strings.length := by
  sorry

-- LLM HELPER
lemma find_longest_aux_maximal (strings: List String) (idx best_idx: Nat) (best_len: Nat) :
  best_idx < strings.length →
  idx ≤ strings.length →
  (∀ j, j < idx → strings[j]!.length ≤ best_len) →
  let result_idx := find_longest_aux strings idx best_idx best_len
  ∀ j, j < strings.length → strings[j]!.length ≤ strings[result_idx]!.length := by
  sorry

-- LLM HELPER
lemma find_longest_aux_earliest (strings: List String) (idx best_idx: Nat) (best_len: Nat) :
  best_idx < strings.length →
  idx ≤ strings.length →
  (∀ j, j < best_idx → strings[j]!.length < best_len) →
  let result_idx := find_longest_aux strings idx best_idx best_len
  ∀ j, j < result_idx → strings[j]!.length < strings[result_idx]!.length := by
  sorry

theorem correctness
(strings: List String)
: problem_spec implementation strings := by
  unfold problem_spec implementation
  cases strings with
  | nil => 
    simp [find_longest_aux]
    use none
    constructor
    · rfl
    · left
      simp
  | cons h t =>
    simp [find_longest_aux]
    let best_idx := find_longest_aux strings 0 0 h.length
    use some (strings[best_idx]!)
    constructor
    · rfl
    · right
      use strings[best_idx]!
      constructor
      · rfl
      · constructor
        · sorry -- strings[best_idx]! ∈ strings
        · intro s hs hlen
          constructor
          · have : best_idx < strings.length := by
              sorry -- follows from find_longest_aux_valid
            use best_idx
            constructor
            · exact this
            · constructor
              · rfl
              · sorry -- follows from find_longest_aux_earliest
          · sorry -- follows from find_longest_aux_maximal