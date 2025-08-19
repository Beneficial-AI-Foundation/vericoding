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
  if idx >= strings.length then best_idx
  else
    let s := strings[idx]!
    if s.length > best_len then
      find_longest_aux strings (idx + 1) idx s.length
    else
      find_longest_aux strings (idx + 1) best_idx best_len
termination_by strings.length - idx

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
  induction idx using Nat.strong_induction_on generalizing best_idx best_len with
  | ind idx ih =>
    intro h1 h2
    unfold find_longest_aux
    simp
    split
    · exact h1
    · simp at *
      split <;> {
        apply ih
        · omega
        · simp at *; omega
        · omega
      }

-- LLM HELPER
lemma find_longest_aux_maximal (strings: List String) (idx best_idx: Nat) (best_len: Nat) :
  best_idx < strings.length →
  idx ≤ strings.length →
  strings[best_idx]!.length = best_len →
  (∀ j, j < idx → strings[j]!.length ≤ best_len) →
  let result_idx := find_longest_aux strings idx best_idx best_len
  ∀ j, j < strings.length → strings[j]!.length ≤ strings[result_idx]!.length := by
  induction idx using Nat.strong_induction_on generalizing best_idx best_len with
  | ind idx ih =>
    intro h1 h2 h3 h4 j hj
    unfold find_longest_aux
    simp
    split
    · rw [h3]; exact h4 j hj
    · simp at *
      split <;> {
        apply ih
        · omega
        · simp at *; omega
        · omega
        · simp [List.get!]; omega
        · intro k hk
          if hk_eq : k < idx then
            exact h4 k hk_eq
          else
            simp at hk_eq
            have : k = idx := by omega
            rw [this]
            simp [List.get!]
            split <;> omega
      }

-- LLM HELPER
lemma find_longest_aux_earliest (strings: List String) (idx best_idx: Nat) (best_len: Nat) :
  best_idx < strings.length →
  idx ≤ strings.length →
  strings[best_idx]!.length = best_len →
  (∀ j, j < best_idx → strings[j]!.length < best_len) →
  let result_idx := find_longest_aux strings idx best_idx best_len
  ∀ j, j < result_idx → strings[j]!.length < strings[result_idx]!.length := by
  induction idx using Nat.strong_induction_on generalizing best_idx best_len with
  | ind idx ih =>
    intro h1 h2 h3 h4 j hj
    unfold find_longest_aux
    simp
    split
    · rw [h3]; exact h4 j hj
    · simp at *
      split <;> {
        apply ih
        · omega
        · simp at *; omega
        · omega
        · simp [List.get!]; omega
        · intro k hk
          if hk_lt : k < idx then
            if hk_best : k < best_idx then
              exact h4 k hk_best
            else
              simp at hk_best
              have : k = best_idx := by omega
              rw [this, h3]
              simp [List.get!]
              split <;> omega
          else
            simp at hk_lt
            have : k = idx := by omega
            rw [this]
            simp [List.get!]
            split <;> omega
      }

-- LLM HELPER
lemma mem_of_get (strings: List String) (i: Nat) (h: i < strings.length) : 
  strings[i]! ∈ strings := by
  simp [List.mem_iff_get]
  use i, h
  simp [List.get!]

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
        · have hvalid : best_idx < strings.length := by
            apply find_longest_aux_valid
            · simp
            · simp
          exact mem_of_get strings best_idx hvalid
        · intro s hs hlen
          have hvalid : best_idx < strings.length := by
            apply find_longest_aux_valid
            · simp
            · simp
          use best_idx
          constructor
          · exact hvalid
          · constructor
            · rfl
            · apply find_longest_aux_earliest
              · simp
              · simp
              · simp
              · intro j hj
                simp at hj
                omega