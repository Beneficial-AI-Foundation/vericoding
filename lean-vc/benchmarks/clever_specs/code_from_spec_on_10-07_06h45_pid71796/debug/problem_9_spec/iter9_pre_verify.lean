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

def implementation (numbers: List Int) : List Int := 
  match numbers with
  | [] => []
  | x :: xs => 
    let rec helper (acc : Int) (rest : List Int) : List Int :=
      match rest with
      | [] => [acc]
      | y :: ys => acc :: helper (max acc y) ys
    helper x xs

-- LLM HELPER
lemma implementation_length (numbers: List Int) :
  (implementation numbers).length = numbers.length := by
  cases numbers with
  | nil => simp [implementation]
  | cons x xs => 
    simp [implementation]
    let rec helper_length (acc : Int) (rest : List Int) : 
      (implementation.helper acc rest).length = rest.length + 1 := by
      cases rest with
      | nil => simp [implementation.helper]
      | cons y ys => 
        simp [implementation.helper]
        rw [helper_length]
        simp
    rw [helper_length]
    simp

-- LLM HELPER
lemma implementation_get_in_take (numbers: List Int) (i : Nat) :
  i < numbers.length →
  (implementation numbers)[i]?.getD 0 ∈ List.take (i + 1) numbers := by
  intro h
  cases numbers with
  | nil => simp at h
  | cons x xs =>
    simp [implementation]
    induction i generalizing x xs with
    | zero =>
      simp [implementation.helper]
      simp [List.take]
    | succ i' ih =>
      cases xs with
      | nil =>
        simp [implementation.helper]
        simp at h
        cases h
      | cons y ys =>
        simp [implementation.helper]
        simp [List.take]
        right
        have h' : i' < (y :: ys).length := by
          simp at h
          exact Nat.lt_of_succ_lt_succ h
        exact ih (max x y) ys h'

-- LLM HELPER
lemma implementation_monotone (numbers: List Int) (i j : Nat) :
  j ≤ i → i < numbers.length →
  numbers[j]?.getD 0 ≤ (implementation numbers)[i]?.getD 0 := by
  intro h_le h_bound
  cases numbers with
  | nil => simp at h_bound
  | cons x xs =>
    simp [implementation]
    induction i generalizing x xs j with
    | zero =>
      simp at h_le
      cases h_le
      simp [implementation.helper]
    | succ i' ih =>
      cases xs with
      | nil =>
        simp [implementation.helper]
        simp at h_bound
        cases h_bound
      | cons y ys =>
        simp [implementation.helper]
        cases j with
        | zero =>
          simp
          have : x ≤ max x y := by simp [max_def]
          have h_bound' : i' < (y :: ys).length := by
            simp at h_bound
            exact Nat.lt_of_succ_lt_succ h_bound
          have rec_result := ih (max x y) ys 0 (by simp) h_bound'
          simp at rec_result
          trans (max x y)
          exact this
          exact rec_result
        | succ j' =>
          simp
          have h_le' : j' ≤ i' := Nat.le_of_succ_le_succ h_le
          have h_bound' : i' < (y :: ys).length := by
            simp at h_bound
            exact Nat.lt_of_succ_lt_succ h_bound
          exact ih (max x y) ys j' h_le' h_bound'

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
    · rw [← List.getD_get?]
      exact implementation_get_in_take numbers i h
    · intro j hj
      rw [← List.getD_get?, ← List.getD_get?]
      exact implementation_monotone numbers i j hj h