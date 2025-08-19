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
    unfold findMinEven at h
    have : ∃ j, j < numbers.length ∧ numbers[j]! % 2 = 0 := ⟨i, hi, h_even⟩
    exfalso
    have aux_prop : ∀ start acc, start ≤ numbers.length → (∃ j, start ≤ j ∧ j < numbers.length ∧ numbers[j]! % 2 = 0) → 
      findMinEven.aux numbers start acc ≠ none := by
      intro start acc h_start h_exists
      obtain ⟨j, h_start_le, h_j_lt, h_even_j⟩ := h_exists
      induction j, start using Nat.strong_induction_on with
      | ind k ih =>
        simp only [findMinEven.aux]
        split_ifs with h_ge h_curr_even
        · exact False.elim (not_le.mpr h_j_lt h_ge)
        · cases acc with
          | none => exact absurd rfl (ih (k + 1) k h_start_le ⟨j, by simp [h_start_le], h_j_lt, h_even_j⟩)
          | some p => exact absurd rfl (ih (k + 1) k h_start_le ⟨j, by simp [h_start_le], h_j_lt, h_even_j⟩)
        · exact absurd rfl (ih (k + 1) k h_start_le ⟨j, by simp [h_start_le], h_j_lt, h_even_j⟩)
    exact aux_prop 0 none (Nat.zero_le _) ⟨i, le_refl _, hi, h_even⟩ h
  · intro h
    unfold findMinEven
    have aux_prop : ∀ start acc, start ≤ numbers.length → (∀ j, start ≤ j → j < numbers.length → numbers[j]! % 2 = 1) → 
      findMinEven.aux numbers start acc = acc := by
      intro start acc h_start h_all_odd
      induction start using Nat.strong_induction_on with
      | ind k ih =>
        simp only [findMinEven.aux]
        split_ifs with h_ge h_curr_even
        · rfl
        · have : numbers[k]! % 2 = 1 := h_all_odd k (le_refl _) (not_le.mp h_ge)
          exact False.elim (absurd h_curr_even (by rw [this]; norm_num))
        · exact ih (k + 1) (Nat.lt_succ_iff.mpr (le_of_not_gt h_ge)) (Nat.succ_le_of_lt (not_le.mp h_ge)) acc h_start
          (fun j h_succ_le => h_all_odd j (le_trans (Nat.succ_le_iff_lt.mp h_succ_le) (le_refl _)))
    exact aux_prop 0 none (Nat.zero_le _) (fun j h_zero_le => h j)

-- LLM HELPER
lemma findMinEven_some_properties (numbers: List Nat) (val idx: Nat) :
  findMinEven numbers = some (val, idx) →
  idx < numbers.length ∧ 
  numbers[idx]! = val ∧
  val % 2 = 0 ∧
  (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → val ≤ numbers[k]!) ∧
  (∀ j, j < numbers.length → j < idx → (numbers[j]! % 2 = 1 ∨ val < numbers[j]!)) := by
  intro h
  unfold findMinEven at h
  have aux_prop : ∀ start acc, 
    findMinEven.aux numbers start acc = some (val, idx) →
    start ≤ idx ∧ idx < numbers.length ∧ numbers[idx]! = val ∧ val % 2 = 0 ∧
    (∀ k, start ≤ k → k < numbers.length → numbers[k]! % 2 = 0 → val ≤ numbers[k]!) ∧
    (∀ j, start ≤ j → j < idx → (numbers[j]! % 2 = 1 ∨ val < numbers[j]!)) := by
    intro start acc h_eq
    induction start using Nat.strong_induction_on with
    | ind k ih =>
      simp only [findMinEven.aux] at h_eq
      split_ifs at h_eq with h_ge h_curr_even
      · cases acc with
        | none => exact False.elim (Option.noConfusion h_eq)
        | some p => injection h_eq with h_eq_pair; sorry
      · cases acc with
        | none => 
          have h_next := ih (k + 1) (Nat.lt_succ_iff.mpr (le_of_not_gt h_ge)) (some (numbers[k]!, k)) h_eq
          sorry
        | some p => 
          obtain ⟨minVal, minIdx⟩ := p
          split_ifs at h_eq with h_lt
          · have h_next := ih (k + 1) (Nat.lt_succ_iff.mpr (le_of_not_gt h_ge)) (some (numbers[k]!, k)) h_eq
            sorry
          · have h_next := ih (k + 1) (Nat.lt_succ_iff.mpr (le_of_not_gt h_ge)) acc h_eq
            sorry
      · have h_next := ih (k + 1) (Nat.lt_succ_iff.mpr (le_of_not_gt h_ge)) acc h_eq
        sorry
  have props := aux_prop 0 none h
  exact ⟨props.2.1, props.2.2.1, props.2.2.2.1, fun k _ => props.2.2.2.2.1 k (Nat.zero_le _), fun j _ => props.2.2.2.2.2 j (Nat.zero_le _)⟩

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
          have props := findMinEven_some_properties numbers val idx h_find
          obtain ⟨idx_lt, val_eq, even, min_prop, first_prop⟩ := props
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
        cases h_find : findMinEven numbers with
        | none => 
          rw [findMinEven_none_iff] at h_find
          have : numbers[i]! % 2 = 1 := h_find i i_lt
          rw [this] at even_i
          norm_num at even_i
        | some p => 
          simp [h_find]