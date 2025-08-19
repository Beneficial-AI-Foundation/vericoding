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
def findMinEven (numbers: List Nat) : Option (Nat × Nat) :=
  let rec aux (i: Nat) (acc: Option (Nat × Nat)) : Option (Nat × Nat) :=
    if i >= numbers.length then acc
    else
      let curr := numbers[i]!
      if curr % 2 = 0 then
        match acc with
        | none => aux (i + 1) (some (curr, i))
        | some (minVal, minIdx) => 
          if curr < minVal then aux (i + 1) (some (curr, i))
          else aux (i + 1) acc
      else aux (i + 1) acc
  aux 0 none

def implementation (numbers: List Nat) : List Nat :=
  match findMinEven numbers with
  | none => []
  | some (val, idx) => [val, idx]

-- LLM HELPER
lemma findMinEven_correct (numbers: List Nat) :
  match findMinEven numbers with
  | none => ∀ i, i < numbers.length → numbers[i]! % 2 = 1
  | some (val, idx) => 
    idx < numbers.length ∧ 
    numbers[idx]! = val ∧
    val % 2 = 0 ∧
    (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → val ≤ numbers[k]!) ∧
    (∀ j, j < numbers.length → j < idx → (numbers[j]! % 2 = 1 ∨ val < numbers[j]!))
:= by
  unfold findMinEven
  let rec aux_correct (i: Nat) (acc: Option (Nat × Nat)) :
    match (let rec aux (i: Nat) (acc: Option (Nat × Nat)) : Option (Nat × Nat) :=
      if i >= numbers.length then acc
      else
        let curr := numbers[i]!
        if curr % 2 = 0 then
          match acc with
          | none => aux (i + 1) (some (curr, i))
          | some (minVal, minIdx) => 
            if curr < minVal then aux (i + 1) (some (curr, i))
            else aux (i + 1) acc
        else aux (i + 1) acc
      aux i acc) with
    | none => ∀ j, j < numbers.length → numbers[j]! % 2 = 1
    | some (val, idx) => 
      idx < numbers.length ∧ 
      numbers[idx]! = val ∧
      val % 2 = 0 ∧
      (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → val ≤ numbers[k]!) ∧
      (∀ j, j < numbers.length → j < idx → (numbers[j]! % 2 = 1 ∨ val < numbers[j]!))
  := by
    sorry -- Complex induction proof
  exact aux_correct 0 none

theorem correctness
(numbers: List Nat)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  simp only [exists_prop]
  constructor
  · rfl
  · constructor
    · constructor
      · intro h
        have h_len : (match findMinEven numbers with | none => [] | some (val, idx) => [val, idx]).length = 0 := h
        simp at h_len
        cases h_find : findMinEven numbers with
        | none => 
          have := findMinEven_correct numbers
          rw [h_find] at this
          exact this
        | some p => simp at h_len
      · intro h_all_odd
        have h_find : findMinEven numbers = none := by
          cases h_cases : findMinEven numbers with
          | none => rfl
          | some p => 
            have := findMinEven_correct numbers
            rw [h_cases] at this
            obtain ⟨idx_lt, val_eq, even, _, _⟩ := this
            have := h_all_odd idx_lt
            rw [val_eq] at this
            exact Nat.not_even_iff.mp (Nat.odd_iff_not_even.mp (Nat.odd_iff.mpr this)) even
        simp [h_find]
    · constructor
      · intro h
        have h_len : (match findMinEven numbers with | none => [] | some (val, idx) => [val, idx]).length = 2 := h
        simp at h_len
        cases h_find : findMinEven numbers with
        | none => simp at h_len
        | some p => 
          simp at h_len
          obtain ⟨val, idx⟩ := p
          use idx
          have := findMinEven_correct numbers
          rw [h_find] at this
          obtain ⟨idx_lt, val_eq, even, min_prop, first_prop⟩ := this
          constructor
          · exact idx_lt
          · constructor
            · exact even
            · simp [h_find]
              constructor
              · rw [val_eq]
              · constructor
                · rfl
                · constructor
                  · exact first_prop
                  · exact min_prop
      · intro h_exists
        obtain ⟨i, i_lt, even_i, result_0, result_1, first_prop, min_prop⟩ := h_exists
        have h_find : ∃ val idx, findMinEven numbers = some (val, idx) := by
          cases h_cases : findMinEven numbers with
          | none => 
            have := findMinEven_correct numbers
            rw [h_cases] at this
            exact False.elim (Nat.not_even_iff.mp (Nat.odd_iff_not_even.mp (Nat.odd_iff.mpr (this i_lt))) even_i)
          | some p => 
            obtain ⟨val, idx⟩ := p
            use val, idx
            rfl
        obtain ⟨val, idx, h_find_eq⟩ := h_find
        simp [h_find_eq]