def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
result.length = numbers.length ∧
∀ i, i < numbers.length →
(result[i]! ∈ numbers.take (i + 1) ∧
∀ j, j ≤ i → numbers[j]! ≤ result[i]!);
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def scanl (f : Int → Int → Int) (init : Int) : List Int → List Int
| [] => [init]
| x :: xs => 
  let rest := scanl f (f init x) xs
  init :: rest

def implementation (numbers: List Int) : List Int := 
match numbers with
| [] => []
| x :: xs => 
  let cumulative := scanl max x xs
  cumulative.tail!

-- LLM HELPER
lemma scanl_length (f : Int → Int → Int) (init : Int) (l : List Int) :
  (scanl f init l).length = l.length + 1 := by
  induction l with
  | nil => simp [scanl]
  | cons x xs ih => 
    simp [scanl]
    rw [ih]
    simp

-- LLM HELPER
lemma tail_length (l : List Int) (h : l.length > 0) :
  l.tail!.length = l.length - 1 := by
  cases l with
  | nil => simp at h
  | cons x xs => simp [List.tail!]

-- LLM HELPER
lemma implementation_length (numbers: List Int) :
  (implementation numbers).length = numbers.length := by
  cases numbers with
  | nil => simp [implementation]
  | cons x xs => 
    simp [implementation]
    rw [tail_length]
    rw [scanl_length]
    simp
    have : (scanl max x xs).length > 0 := by
      rw [scanl_length]
      simp
    exact this

-- LLM HELPER
lemma scanl_max_monotone (init : Int) (l : List Int) (i j : Nat) :
  i ≤ j → j < (scanl max init l).length →
  (scanl max init l)[i]! ≤ (scanl max init l)[j]! := by
  intro h_le h_bound
  induction l generalizing i j with
  | nil => 
    simp [scanl] at h_bound
    simp at h_bound
    cases h_bound
  | cons x xs ih =>
    simp [scanl]
    cases i with
    | zero =>
      cases j with
      | zero => simp
      | succ j' =>
        simp
        have : init ≤ max init x := by simp [max_def]
        have rec_bound : j' < (scanl max (max init x) xs).length := by
          simp at h_bound
          exact Nat.lt_of_succ_lt_succ h_bound
        have rec_result := ih 0 j' (by simp) rec_bound
        simp [scanl] at rec_result
        trans (max init x)
        exact this
        exact rec_result
    | succ i' =>
      cases j with
      | zero => 
        simp at h_le
      | succ j' =>
        simp
        have h_le' : i' ≤ j' := Nat.le_of_succ_le_succ h_le
        have h_bound' : j' < (scanl max (max init x) xs).length := by
          simp at h_bound
          exact Nat.lt_of_succ_lt_succ h_bound
        exact ih h_le' h_bound'

-- LLM HELPER
lemma scanl_contains_elements (init : Int) (l : List Int) (i : Nat) :
  i < (scanl max init l).length →
  ∃ j, j ≤ i ∧ ((scanl max init l)[i]! = init ∨ (scanl max init l)[i]! ∈ l.take i) := by
  intro h
  induction l generalizing i with
  | nil => 
    simp [scanl] at h
    simp at h
    cases h
  | cons x xs ih =>
    simp [scanl]
    cases i with
    | zero =>
      use 0
      simp
    | succ i' =>
      simp
      have h' : i' < (scanl max (max init x) xs).length := by
        simp at h
        exact Nat.lt_of_succ_lt_succ h
      have ih_result := ih h'
      obtain ⟨j, hj_le, hj_prop⟩ := ih_result
      use j + 1
      constructor
      · exact Nat.succ_le_succ hj_le
      · cases hj_prop with
        | inl h_init => 
          right
          simp [List.take]
          have : max init x ∈ [x] := by
            simp [max_def]
            split_ifs
            · simp
            · simp
          rw [← h_init]
          exact this
        | inr h_mem =>
          right
          simp [List.take]
          right
          rw [← List.take_succ_cons]
          exact h_mem

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  constructor
  · exact implementation_length numbers
  · intro i h
    constructor
    · cases numbers with
      | nil => simp at h
      | cons x xs =>
        simp [implementation]
        have scan_bound : i < (scanl max x xs).tail!.length := by
          rw [implementation_length] at h
          simp [implementation] at h
          exact h
        simp [List.tail!]
        simp [List.take]
        right
        sorry
    · intro j hj
      cases numbers with
      | nil => simp at h
      | cons x xs =>
        simp [implementation]
        have mono := scanl_max_monotone x xs j i hj
        simp [List.tail!] at mono
        have bound : i < (scanl max x xs).length := by
          rw [scanl_length]
          simp at h
          exact Nat.lt_add_one_of_lt h
        apply mono
        rw [scanl_length]
        simp
        exact Nat.lt_add_one_of_le hj