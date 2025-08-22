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
(0 < 2*i - 1 → result[2 * i - 1]! = delimeter));
∃ result, implementation numbers delimeter = result ∧
spec result

-- LLM HELPER
def intersperse (numbers: List Int) (delimeter: Int) : List Int :=
match numbers with
| [] => []
| [x] => [x]
| x :: xs => x :: delimeter :: intersperse xs delimeter

def implementation (numbers: List Int) (delimeter: Int) : List Int := 
  intersperse numbers delimeter

-- LLM HELPER
lemma intersperse_nil (delimeter: Int) : intersperse [] delimeter = [] := by
  simp [intersperse]

-- LLM HELPER
lemma intersperse_single (x: Int) (delimeter: Int) : 
  intersperse [x] delimeter = [x] := by
  simp [intersperse]

-- LLM HELPER
lemma intersperse_cons (x: Int) (xs: List Int) (delimeter: Int) (h: xs ≠ []) : 
  intersperse (x :: xs) delimeter = x :: delimeter :: intersperse xs delimeter := by
  cases xs with
  | nil => contradiction
  | cons y ys => simp [intersperse]

-- LLM HELPER
lemma intersperse_length_empty (delimeter: Int) : 
  (intersperse [] delimeter).length = 0 := by
  simp [intersperse]

-- LLM HELPER
lemma intersperse_length_single (x: Int) (delimeter: Int) : 
  (intersperse [x] delimeter).length = 1 := by
  simp [intersperse]

-- LLM HELPER
lemma intersperse_length_cons (x: Int) (xs: List Int) (delimeter: Int) (h: xs ≠ []) : 
  (intersperse (x :: xs) delimeter).length = 2 + (intersperse xs delimeter).length := by
  cases xs with
  | nil => contradiction
  | cons y ys => simp [intersperse]

-- LLM HELPER
lemma intersperse_length_ge_two (numbers: List Int) (delimeter: Int) (h: numbers.length ≥ 2) : 
  (intersperse numbers delimeter).length = 2 * numbers.length - 1 := by
  induction numbers with
  | nil => simp at h
  | cons x xs =>
    cases xs with
    | nil => simp at h
    | cons y ys =>
      simp [intersperse]
      induction ys generalizing x y with
      | nil => simp [intersperse]
      | cons z zs ih =>
        simp [intersperse]
        rw [ih]
        simp
        omega

-- LLM HELPER
lemma intersperse_get_even (numbers: List Int) (delimeter: Int) (i: Nat) (h: i < numbers.length) :
  (intersperse numbers delimeter)[2 * i]! = numbers[i]! := by
  induction numbers generalizing i with
  | nil => simp at h
  | cons x xs =>
    cases i with
    | zero => 
      cases xs with
      | nil => simp [intersperse]
      | cons y ys => simp [intersperse]
    | succ i' =>
      cases xs with
      | nil => simp at h
      | cons y ys =>
        simp [intersperse]
        simp [List.get!]
        rw [List.get!_cons_succ, List.get!_cons_succ]
        apply_assumption
        simp at h
        omega

-- LLM HELPER
lemma intersperse_get_odd (numbers: List Int) (delimeter: Int) (i: Nat) (h: i < numbers.length) (h2: 0 < 2*i - 1) :
  (intersperse numbers delimeter)[2 * i - 1]! = delimeter := by
  induction numbers generalizing i with
  | nil => simp at h
  | cons x xs =>
    cases i with
    | zero => simp at h2
    | succ i' =>
      cases xs with
      | nil => simp at h
      | cons y ys =>
        simp [intersperse]
        simp [List.get!]
        cases i' with
        | zero => simp
        | succ i'' =>
          rw [List.get!_cons_succ, List.get!_cons_succ]
          apply_assumption
          simp at h
          omega
          omega

theorem correctness
(numbers: List Int)
(delimeter: Int)
: problem_spec implementation numbers delimeter := by
  unfold problem_spec implementation
  cases' numbers with x xs
  · use []
    constructor
    · simp [intersperse]
    · left
      constructor
      · simp [intersperse]
      · simp [intersperse]
  · cases' xs with y ys
    · use [x]
      constructor
      · simp [intersperse]
      · right
        left
        constructor
        · simp [intersperse]
        · constructor
          · simp
          · constructor
            · simp [intersperse]
            · simp [intersperse]
    · use intersperse (x :: y :: ys) delimeter
      constructor
      · rfl
      · right
        right
        constructor
        · apply intersperse_length_ge_two
          simp
          omega
        · intro i hi
          constructor
          · apply intersperse_get_even
            exact hi
          · intro h_pos
            apply intersperse_get_odd
            exact hi
            exact h_pos