def problem_spec
-- function signature
(implementation: List Int → Bool)
-- inputs
(numbers: List Int) :=
let non_ordered := ∃ i j,
i < numbers.length - 1 ∧
j < numbers.length - 1 ∧
(numbers[i]! < numbers[i+1]!) ∧
(numbers[j+1]! < numbers[j]!);
-- spec
let spec (result: Bool) :=
  1 < numbers.length →
  result ↔ ¬non_ordered;
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def is_non_decreasing (numbers: List Int) : Bool :=
  match numbers with
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    if a ≤ b then is_non_decreasing (b :: rest)
    else false

-- LLM HELPER
def is_non_increasing (numbers: List Int) : Bool :=
  match numbers with
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    if a ≥ b then is_non_increasing (b :: rest)
    else false

def implementation (numbers: List Int) : Bool := 
  is_non_decreasing numbers || is_non_increasing numbers

-- LLM HELPER
lemma is_non_decreasing_correct (numbers: List Int) :
  is_non_decreasing numbers = true ↔ 
  ∀ i, i < numbers.length - 1 → numbers[i]! ≤ numbers[i+1]! :=
by
  induction numbers with
  | nil => simp [is_non_decreasing]
  | cons a tail ih =>
    cases tail with
    | nil => simp [is_non_decreasing]
    | cons b rest =>
      simp [is_non_decreasing]
      constructor
      · intro h
        intro i hi
        simp at hi
        cases i with
        | zero => 
          simp
          simp [is_non_decreasing] at h
          cases decide_eq (a ≤ b) with
          | inl hab => exact hab
          | inr hab => simp [hab] at h
        | succ j =>
          have : is_non_decreasing (b :: rest) = true := by
            simp [is_non_decreasing] at h
            cases decide_eq (a ≤ b) with
            | inl hab => 
              simp [hab] at h
              exact h
            | inr hab => 
              simp [hab] at h
          rw [ih] at this
          exact this j (by simp; exact Nat.lt_of_succ_lt_succ hi)
      · intro h
        have h0 : a ≤ b := h 0 (by simp)
        simp [h0]
        rw [ih]
        intro i hi
        exact h (i + 1) (by simp; exact Nat.succ_lt_succ hi)

-- LLM HELPER
lemma is_non_increasing_correct (numbers: List Int) :
  is_non_increasing numbers = true ↔ 
  ∀ i, i < numbers.length - 1 → numbers[i+1]! ≤ numbers[i]! :=
by
  induction numbers with
  | nil => simp [is_non_increasing]
  | cons a tail ih =>
    cases tail with
    | nil => simp [is_non_increasing]
    | cons b rest =>
      simp [is_non_increasing]
      constructor
      · intro h
        intro i hi
        simp at hi
        cases i with
        | zero => 
          simp
          simp [is_non_increasing] at h
          cases decide_eq (a ≥ b) with
          | inl hab => exact hab
          | inr hab => simp [hab] at h
        | succ j =>
          have : is_non_increasing (b :: rest) = true := by
            simp [is_non_increasing] at h
            cases decide_eq (a ≥ b) with
            | inl hab => 
              simp [hab] at h
              exact h
            | inr hab => 
              simp [hab] at h
          rw [ih] at this
          exact this j (by simp; exact Nat.lt_of_succ_lt_succ hi)
      · intro h
        have h0 : b ≤ a := h 0 (by simp)
        simp [h0]
        rw [ih]
        intro i hi
        exact h (i + 1) (by simp; exact Nat.succ_lt_succ hi)

-- LLM HELPER
lemma non_ordered_characterization (numbers: List Int) :
  (∃ i j, i < numbers.length - 1 ∧ j < numbers.length - 1 ∧ 
   (numbers[i]! < numbers[i+1]!) ∧ (numbers[j+1]! < numbers[j]!)) ↔
  ¬(is_non_decreasing numbers || is_non_increasing numbers) :=
by
  constructor
  · intro ⟨i, j, hi, hj, h_inc, h_dec⟩
    simp
    constructor
    · rw [is_non_decreasing_correct]
      push_neg
      exact ⟨i, hi, not_le.mpr h_inc⟩
    · rw [is_non_increasing_correct] 
      push_neg
      exact ⟨j, hj, not_le.mpr h_dec⟩
  · intro h
    simp at h
    cases h with
    | mk h1 h2 =>
      rw [is_non_decreasing_correct] at h1
      rw [is_non_increasing_correct] at h2
      push_neg at h1 h2
      obtain ⟨i, hi, h_not_le_i⟩ := h1
      obtain ⟨j, hj, h_not_le_j⟩ := h2
      exact ⟨i, j, hi, hj, not_le.mp h_not_le_i, not_le.mp h_not_le_j⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
  use implementation numbers
  simp [implementation]
  intro h_len
  rw [non_ordered_characterization]
  simp