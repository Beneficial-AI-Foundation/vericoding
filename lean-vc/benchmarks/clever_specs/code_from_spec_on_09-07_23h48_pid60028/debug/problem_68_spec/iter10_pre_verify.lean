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
  unfold find_min_even
  sorry

theorem correctness
(numbers: List Nat)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  use (match find_min_even numbers with
      | none => []
      | some (val, idx) => [val, idx])
  constructor
  · rfl
  · simp only [List.length_nil, List.length_cons, List.length_singleton]
    cases h_find : find_min_even numbers with
    | none => 
      simp [h_find]
      have all_odd := find_min_even_correct numbers
      rw [h_find] at all_odd
      constructor
      · intro h
        exact all_odd
      · intro h
        exfalso
        obtain ⟨i, hi_lt, hi_even, _, _, _, _⟩ := h
        have : numbers[i]! % 2 = 1 := all_odd i hi_lt
        rw [this] at hi_even
        norm_num at hi_even
    | some p =>
      simp [h_find]
      let ⟨val, idx⟩ := p
      have min_even := find_min_even_correct numbers
      rw [h_find] at min_even
      constructor
      · intro h
        exfalso
        norm_num at h
      · intro h
        use idx
        constructor
        · exact min_even.1
        · constructor
          · exact min_even.2.2.1
          · constructor
            · simp [List.getElem_cons_zero]
              exact min_even.2.1
            · constructor
              · simp [List.getElem_cons_one]
              · constructor
                · exact min_even.2.2.2.1
                · exact min_even.2.2.2.2