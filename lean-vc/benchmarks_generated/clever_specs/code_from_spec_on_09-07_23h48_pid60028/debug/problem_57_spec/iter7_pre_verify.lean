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
def is_monotonic_asc (numbers: List Int) : Bool :=
  match numbers with
  | [] => true
  | [_] => true
  | x :: y :: rest => x <= y && is_monotonic_asc (y :: rest)

-- LLM HELPER
def is_monotonic_desc (numbers: List Int) : Bool :=
  match numbers with
  | [] => true
  | [_] => true
  | x :: y :: rest => x >= y && is_monotonic_desc (y :: rest)

-- LLM HELPER
def is_monotonic (numbers: List Int) : Bool :=
  is_monotonic_asc numbers || is_monotonic_desc numbers

def implementation (numbers: List Int) : Bool := is_monotonic numbers

-- LLM HELPER
lemma is_monotonic_asc_no_dec (numbers: List Int) :
  is_monotonic_asc numbers = true →
  ¬∃ i, i < numbers.length - 1 ∧ numbers[i+1]! < numbers[i]! := by
  intro h
  intro ⟨i, hi, h_dec⟩
  induction numbers generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases xs with
    | nil => simp at hi
    | cons y ys =>
      simp [is_monotonic_asc] at h
      cases h with
      | intro h_xy h_rest =>
        cases i with
        | zero => 
          simp at h_dec
          linarith [h_xy, h_dec]
        | succ i' =>
          simp at h_dec hi
          apply ih h_rest
          use i'
          constructor
          · exact Nat.lt_pred_of_succ_lt hi
          · exact h_dec

-- LLM HELPER
lemma is_monotonic_desc_no_inc (numbers: List Int) :
  is_monotonic_desc numbers = true →
  ¬∃ i, i < numbers.length - 1 ∧ numbers[i]! < numbers[i+1]! := by
  intro h
  intro ⟨i, hi, h_inc⟩
  induction numbers generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases xs with
    | nil => simp at hi
    | cons y ys =>
      simp [is_monotonic_desc] at h
      cases h with
      | intro h_xy h_rest =>
        cases i with
        | zero => 
          simp at h_inc
          linarith [h_xy, h_inc]
        | succ i' =>
          simp at h_inc hi
          apply ih h_rest
          use i'
          constructor
          · exact Nat.lt_pred_of_succ_lt hi
          · exact h_inc

-- LLM HELPER
lemma not_monotonic_asc_exists_dec (numbers: List Int) :
  numbers.length > 1 →
  is_monotonic_asc numbers = false →
  ∃ i, i < numbers.length - 1 ∧ numbers[i+1]! < numbers[i]! := by
  intro h_len h_not_asc
  induction numbers with
  | nil => simp at h_len
  | cons x xs ih =>
    cases xs with
    | nil => simp at h_len
    | cons y ys =>
      simp [is_monotonic_asc] at h_not_asc
      cases h_not_asc with
      | inl h_xy =>
        use 0
        simp
        constructor
        · simp [List.length]
          omega
        · exact h_xy
      | inr h_rest =>
        have h_len_xs : xs.length > 1 := by
          simp [List.length] at h_len
          omega
        have ⟨i, hi, h_dec⟩ := ih h_len_xs h_rest
        use i + 1
        constructor
        · simp [List.length]
          omega
        · simp
          exact h_dec

-- LLM HELPER
lemma not_monotonic_desc_exists_inc (numbers: List Int) :
  numbers.length > 1 →
  is_monotonic_desc numbers = false →
  ∃ i, i < numbers.length - 1 ∧ numbers[i]! < numbers[i+1]! := by
  intro h_len h_not_desc
  induction numbers with
  | nil => simp at h_len
  | cons x xs ih =>
    cases xs with
    | nil => simp at h_len
    | cons y ys =>
      simp [is_monotonic_desc] at h_not_desc
      cases h_not_desc with
      | inl h_xy =>
        use 0
        simp
        constructor
        · simp [List.length]
          omega
        · exact h_xy
      | inr h_rest =>
        have h_len_xs : xs.length > 1 := by
          simp [List.length] at h_len
          omega
        have ⟨i, hi, h_inc⟩ := ih h_len_xs h_rest
        use i + 1
        constructor
        · simp [List.length]
          omega
        · simp
          exact h_inc

-- LLM HELPER
lemma is_monotonic_correct (numbers: List Int) : 
  1 < numbers.length → 
  (is_monotonic numbers ↔ ¬∃ i j, i < numbers.length - 1 ∧ j < numbers.length - 1 ∧ 
    (numbers[i]! < numbers[i+1]!) ∧ (numbers[j+1]! < numbers[j]!)) := by
  intro h
  constructor
  · intro h_mono
    intro ⟨i, j, hi, hj, h_inc, h_dec⟩
    simp [is_monotonic] at h_mono
    cases h_mono with
    | inl h_asc => 
      have := is_monotonic_asc_no_dec numbers h_asc
      apply this
      use j
      exact ⟨hj, h_dec⟩
    | inr h_desc =>
      have := is_monotonic_desc_no_inc numbers h_desc
      apply this
      use i
      exact ⟨hi, h_inc⟩
  · intro h_not_non_ordered
    simp [is_monotonic]
    by_contra h_not_mono
    simp at h_not_mono
    cases h_not_mono with
    | intro h_not_asc h_not_desc =>
      have h_len : numbers.length > 1 := by omega
      have ⟨i, hi, h_inc⟩ := not_monotonic_desc_exists_inc numbers h_len h_not_desc
      have ⟨j, hj, h_dec⟩ := not_monotonic_asc_exists_dec numbers h_len h_not_asc
      apply h_not_non_ordered
      use i, j
      exact ⟨hi, hj, h_inc, h_dec⟩

theorem correctness (numbers: List Int) : problem_spec implementation numbers := by
  unfold problem_spec
  use is_monotonic numbers
  constructor
  · rfl
  · intro h
    exact is_monotonic_correct numbers h