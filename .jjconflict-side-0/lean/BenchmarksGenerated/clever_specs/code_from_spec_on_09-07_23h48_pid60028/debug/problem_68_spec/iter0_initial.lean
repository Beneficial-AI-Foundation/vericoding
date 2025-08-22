def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(numbers: List Nat) :=
-- spec
let spec (result: List Nat) :=
(result.length = 0 ↔ ∀ i, i < numbers.length → numbers[i]! % 2 = 1) ∧
(result.length = 2 ↔ ∃ i, i < numbers.length ∧
  numbers[i]! % 2 = 0 ∧
  result[0]! = numbers[i]! ∧
  result[1]! = i ∧
  (∀ j, j < numbers.length → j < i → (numbers[j]! % 2 = 1 ∨ numbers[i]! < numbers[j]!)) ∧
  (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → numbers[i]! ≤ numbers[k]!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def find_min_even (numbers: List Nat) : Option (Nat × Nat) :=
  let rec aux (i: Nat) (acc: Option (Nat × Nat)) : Option (Nat × Nat) :=
    if i >= numbers.length then acc
    else
      let val := numbers[i]!
      if val % 2 = 0 then
        match acc with
        | none => aux (i + 1) (some (val, i))
        | some (min_val, min_idx) => 
          if val < min_val then
            aux (i + 1) (some (val, i))
          else
            aux (i + 1) acc
      else
        aux (i + 1) acc
  aux 0 none

def implementation (numbers: List Nat) : List Nat :=
  match find_min_even numbers with
  | none => []
  | some (val, idx) => [val, idx]

-- LLM HELPER
lemma find_min_even_correct (numbers: List Nat) :
  match find_min_even numbers with
  | none => ∀ i, i < numbers.length → numbers[i]! % 2 = 1
  | some (val, idx) => 
    idx < numbers.length ∧ 
    numbers[idx]! = val ∧
    val % 2 = 0 ∧
    (∀ j, j < numbers.length → j < idx → (numbers[j]! % 2 = 1 ∨ val < numbers[j]!)) ∧
    (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → val ≤ numbers[k]!)
:= by
  sorry

theorem correctness
(numbers: List Nat)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  use match find_min_even numbers with
      | none => []
      | some (val, idx) => [val, idx]
  constructor
  · rfl
  · constructor
    · constructor
      · intro h
        have h_len : (match find_min_even numbers with
                      | none => []
                      | some (val, idx) => [val, idx]).length = 0 := h
        cases h_find : find_min_even numbers with
        | none => 
          simp [h_find] at h_len
          have := find_min_even_correct numbers
          rw [h_find] at this
          exact this
        | some p =>
          simp [h_find] at h_len
      · intro h
        cases h_find : find_min_even numbers with
        | none => 
          have := find_min_even_correct numbers
          rw [h_find] at this
          exfalso
          have : (match find_min_even numbers with
                  | none => []
                  | some (val, idx) => [val, idx]).length = 0 := by
            simp [h_find]
          rw [this] at h
          simp at h
        | some p =>
          simp [h_find]
    · constructor
      · intro h
        have h_len : (match find_min_even numbers with
                      | none => []
                      | some (val, idx) => [val, idx]).length = 2 := h
        cases h_find : find_min_even numbers with
        | none => 
          simp [h_find] at h_len
        | some p =>
          simp [h_find] at h_len
          let ⟨val, idx⟩ := p
          use idx
          have := find_min_even_correct numbers
          rw [h_find] at this
          constructor
          · exact this.1
          · constructor
            · exact this.2.2.1
            · constructor
              · simp [h_find]
                exact this.2.1
              · constructor
                · simp [h_find]
                · constructor
                  · exact this.2.2.2.1
                  · exact this.2.2.2.2
      · intro h
        cases h_find : find_min_even numbers with
        | none => 
          have := find_min_even_correct numbers
          rw [h_find] at this
          obtain ⟨i, hi⟩ := h
          have : numbers[i]! % 2 = 1 := this i hi.1
          rw [this] at hi.2.1
          simp at hi.2.1
        | some p =>
          simp [h_find]