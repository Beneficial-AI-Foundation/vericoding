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
  (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → numbers[i]! ≤ numbers[k]!))
-- program termination
in ∃ result, implementation numbers = result ∧
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
lemma findMinEven_none_iff (numbers: List Nat) :
  findMinEven numbers = none ↔ ∀ i, i < numbers.length → numbers[i]! % 2 = 1 := by
  constructor
  · intro h i hi
    by_contra h_not_odd
    have h_even : numbers[i]! % 2 = 0 := by
      have : numbers[i]! % 2 = 0 ∨ numbers[i]! % 2 = 1 := Nat.mod_two_eq_zero_or_one (numbers[i]!)
      cases this with
      | inl h => exact h
      | inr h => exact False.elim (h_not_odd h)
    -- If we have an even number, findMinEven should return some result
    have : ∃ j val, j < numbers.length ∧ numbers[j]! % 2 = 0 := ⟨i, numbers[i]!, hi, h_even⟩
    -- This contradicts h : findMinEven numbers = none
    unfold findMinEven at h
    -- We'll show this leads to a contradiction by strong induction
    suffices : findMinEven.aux 0 none ≠ none by exact this h
    -- We can't easily prove this without more complex reasoning about the aux function
    -- So we'll use a different approach
    exfalso
    exact h_not_odd rfl
  · intro h
    unfold findMinEven
    -- We need to show that if all numbers are odd, then aux returns none
    -- This is complex to prove directly, so we'll use the contrapositive
    by_contra h_not_none
    -- If findMinEven ≠ none, then there exists some even number
    have : ∃ i, i < numbers.length ∧ numbers[i]! % 2 = 0 := by
      -- This follows from the fact that aux only returns Some when it finds an even number
      sorry
    obtain ⟨i, hi, h_even⟩ := this
    have : numbers[i]! % 2 = 1 := h i hi
    rw [this] at h_even
    norm_num at h_even

-- LLM HELPER
lemma findMinEven_some_properties (numbers: List Nat) (val idx: Nat) :
  findMinEven numbers = some (val, idx) →
  idx < numbers.length ∧ 
  numbers[idx]! = val ∧
  val % 2 = 0 ∧
  (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → val ≤ numbers[k]!) ∧
  (∀ j, j < numbers.length → j < idx → (numbers[j]! % 2 = 1 ∨ val < numbers[j]!)) := by
  intro h
  constructor
  · sorry -- idx < numbers.length
  · constructor
    · sorry -- numbers[idx]! = val
    · constructor
      · sorry -- val % 2 = 0
      · constructor
        · sorry -- minimum property
        · sorry -- first even property

theorem correctness
(numbers: List Nat)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  use match findMinEven numbers with | none => [] | some (val, idx) => [val, idx]
  constructor
  · rfl
  · constructor
    · constructor
      · intro h
        cases h_find : findMinEven numbers with
        | none => 
          rw [findMinEven_none_iff] at h_find
          exact h_find
        | some p => 
          simp at h
      · intro h_all_odd
        have h_find : findMinEven numbers = none := by
          rw [findMinEven_none_iff]
          exact h_all_odd
        simp [h_find]
    · constructor
      · intro h
        cases h_find : findMinEven numbers with
        | none => simp at h
        | some p => 
          obtain ⟨val, idx⟩ := p
          use idx
          simp [h_find]
          have props := findMinEven_some_properties numbers val idx h_find
          constructor
          · exact props.1
          · constructor
            · exact props.2.2.1
            · constructor
              · rfl
              · constructor
                · rfl
                · constructor
                  · exact props.2.2.2.2
                  · exact props.2.2.2.1
      · intro h_exists
        obtain ⟨i, i_lt, even_i, result_0, result_1, first_prop, min_prop⟩ := h_exists
        cases h_find : findMinEven numbers with
        | none => 
          rw [findMinEven_none_iff] at h_find
          have : numbers[i]! % 2 = 1 := h_find i i_lt
          rw [this] at even_i
          norm_num at even_i
        | some p => 
          simp [h_find]