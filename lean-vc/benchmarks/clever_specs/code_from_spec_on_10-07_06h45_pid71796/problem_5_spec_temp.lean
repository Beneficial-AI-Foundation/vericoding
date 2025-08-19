def problem_spec
(implementation: List Int → Int → List Int)
(numbers: List Int)
(delimeter: Int) :=
let spec (result: List Int) :=
(result.length = 0 ∧ result = numbers) ∨
(result.length = 2 ∧ numbers.length = 1 ∧
result[0]! = numbers[0]! ∧ result[1]! = delimeter) ∨
(result.length = 2 * numbers.length - 1 ∧
∀ i, i < numbers.length →
result[2 * i]! = numbers[i]! ∧
(0 < 2*i - 1 → result[2 * i - 1]! = delimeter))
∃ result, implementation numbers delimeter = result ∧
spec result

def implementation (numbers: List Int) (delimeter: Int) : List Int := 
match numbers with
| [] => []
| [x] => [x, delimeter]
| x :: xs => x :: delimeter :: implementation xs delimeter

-- LLM HELPER
lemma implementation_length (numbers: List Int) (delimeter: Int) :
  (numbers = [] → (implementation numbers delimeter).length = 0) ∧
  (numbers.length = 1 → (implementation numbers delimeter).length = 2) ∧
  (numbers.length > 1 → (implementation numbers delimeter).length = 2 * numbers.length - 1) := by
  constructor
  · intro h
    simp [implementation, h]
  constructor
  · intro h
    cases numbers with
    | nil => simp at h
    | cons head tail =>
      cases tail with
      | nil => simp [implementation]
      | cons _ _ => simp [List.length] at h
  · intro h
    induction numbers with
    | nil => simp at h
    | cons head tail ih =>
      cases tail with
      | nil => simp [List.length] at h
      | cons head' tail' =>
        simp [implementation, List.length]
        have : tail.length ≥ 1 := by
          simp [List.length]
          exact Nat.succ_pos tail'.length
        have : tail.length > 1 ∨ tail.length = 1 := by
          cases tail' with
          | nil => right; simp [List.length]
          | cons _ _ => left; simp [List.length]; exact Nat.succ_lt_succ (Nat.succ_pos _)
        cases this with
        | inl h_gt =>
          have := ih.2 h_gt
          simp [this]
          omega
        | inr h_eq =>
          have := ih.1 h_eq
          simp [this]
          omega

-- LLM HELPER
lemma implementation_indexing (numbers: List Int) (delimeter: Int) :
  ∀ i, i < numbers.length →
    (implementation numbers delimeter)[2 * i]! = numbers[i]! ∧
    (0 < 2*i - 1 → (implementation numbers delimeter)[2 * i - 1]! = delimeter) := by
  intro i hi
  induction numbers generalizing i with
  | nil => simp at hi
  | cons head tail ih =>
    cases i with
    | zero =>
      simp [implementation]
      constructor
      · rfl
      · intro h
        simp at h
    | succ i' =>
      simp [implementation, List.length] at hi ⊢
      have hi' : i' < tail.length := Nat.lt_of_succ_lt_succ hi
      have := ih i' hi'
      simp [List.getElem_cons_succ]
      constructor
      · simp [Nat.succ_mul]
        rw [List.getElem_cons_succ, List.getElem_cons_succ]
        exact this.1
      · intro h
        simp [Nat.succ_mul] at h ⊢
        have : 2 * i' + 1 < (implementation tail delimeter).length + 2 := by
          cases tail with
          | nil => simp at hi'
          | cons _ _ =>
            have len_eq := implementation_length tail delimeter
            cases tail with
            | nil => simp at hi'
            | cons _ tail' =>
              cases tail' with
              | nil =>
                have := len_eq.1 rfl
                simp [this]
                omega
              | cons _ _ =>
                have tail_gt : tail.length > 1 := by simp [List.length]; exact Nat.succ_lt_succ (Nat.succ_pos _)
                have := len_eq.2 tail_gt
                simp [this]
                omega
        rw [List.getElem_cons_succ]
        exact this.2 (Nat.succ_pos _)

theorem correctness
(numbers: List Int)
(delimeter: Int)
: problem_spec implementation numbers delimeter := by
  use implementation numbers delimeter
  constructor
  · rfl
  · have len_lemma := implementation_length numbers delimeter
    have idx_lemma := implementation_indexing numbers delimeter
    cases h : numbers with
    | nil =>
      left
      constructor
      · exact len_lemma.1 h
      · simp [implementation, h]
    | cons head tail =>
      cases tail with
      | nil =>
        right
        left
        constructor
        · exact len_lemma.1 rfl
        constructor
        · simp [List.length, h]
        constructor
        · simp [implementation, h]
        · simp [implementation, h]
      | cons head' tail' =>
        right
        right
        constructor
        · have : numbers.length > 1 := by simp [h, List.length]; exact Nat.succ_lt_succ (Nat.succ_pos _)
          exact len_lemma.2 this
        · simp [h]
          exact idx_lemma