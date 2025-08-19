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
def scanMax : List Int → List Int
| [] => []
| x :: xs => 
  let rec helper (acc : Int) (rest : List Int) : List Int :=
    match rest with
    | [] => [acc]
    | y :: ys => acc :: helper (max acc y) ys
  helper x xs

def implementation (numbers: List Int) : List Int := 
  scanMax numbers

-- LLM HELPER
lemma scanMax_length (numbers: List Int) :
  (scanMax numbers).length = numbers.length := by
  cases numbers with
  | nil => simp [scanMax]
  | cons x xs => 
    simp [scanMax]
    let rec helper_length (acc : Int) (rest : List Int) : 
      (scanMax.helper acc rest).length = rest.length + 1 := by
      cases rest with
      | nil => simp [scanMax.helper]
      | cons y ys => 
        simp [scanMax.helper]
        rw [helper_length]
        simp
    rw [helper_length]
    simp

-- LLM HELPER
lemma scanMax_monotone (numbers: List Int) (i j : Nat) :
  i ≤ j → j < numbers.length →
  (scanMax numbers)[i]! ≤ (scanMax numbers)[j]! := by
  intro h_le h_bound
  cases numbers with
  | nil => simp at h_bound
  | cons x xs =>
    simp [scanMax]
    let rec helper_mono (acc : Int) (rest : List Int) (i j : Nat) :
      i ≤ j → j < (scanMax.helper acc rest).length →
      (scanMax.helper acc rest)[i]! ≤ (scanMax.helper acc rest)[j]! := by
      intro h_le h_bound
      cases rest with
      | nil => 
        simp [scanMax.helper] at h_bound
        simp at h_bound
        cases h_bound
      | cons y ys =>
        simp [scanMax.helper]
        cases i with
        | zero =>
          cases j with
          | zero => simp
          | succ j' =>
            simp
            have : acc ≤ max acc y := by simp [max_def]
            have rec_bound : j' < (scanMax.helper (max acc y) ys).length := by
              simp at h_bound
              exact Nat.lt_of_succ_lt_succ h_bound
            have rec_result := helper_mono (max acc y) ys 0 j' (by simp) rec_bound
            simp [scanMax.helper] at rec_result
            trans (max acc y)
            exact this
            exact rec_result
        | succ i' =>
          cases j with
          | zero => 
            simp at h_le
          | succ j' =>
            simp
            have h_le' : i' ≤ j' := Nat.le_of_succ_le_succ h_le
            have h_bound' : j' < (scanMax.helper (max acc y) ys).length := by
              simp at h_bound
              exact Nat.lt_of_succ_lt_succ h_bound
            exact helper_mono (max acc y) ys i' j' h_le' h_bound'
    exact helper_mono x xs i j h_le (by rw [scanMax_length]; exact h_bound)

-- LLM HELPER
lemma scanMax_contains (numbers: List Int) (i : Nat) :
  i < numbers.length →
  (scanMax numbers)[i]! ∈ numbers.take (i + 1) := by
  intro h
  cases numbers with
  | nil => simp at h
  | cons x xs =>
    simp [scanMax]
    let rec helper_contains (acc : Int) (rest : List Int) (orig : List Int) (i : Nat) :
      i < (scanMax.helper acc rest).length →
      acc ∈ orig →
      (scanMax.helper acc rest)[i]! ∈ orig ∨ (scanMax.helper acc rest)[i]! ∈ rest := by
      intro h_bound h_acc
      cases rest with
      | nil => 
        simp [scanMax.helper] at h_bound
        simp at h_bound
        cases h_bound
      | cons y ys =>
        simp [scanMax.helper]
        cases i with
        | zero =>
          left
          exact h_acc
        | succ i' =>
          simp
          have h_bound' : i' < (scanMax.helper (max acc y) ys).length := by
            simp at h_bound
            exact Nat.lt_of_succ_lt_succ h_bound
          have max_mem : max acc y ∈ orig ∨ max acc y ∈ y :: ys := by
            simp [max_def]
            split_ifs with h_cond
            · left; exact h_acc
            · right; simp
          cases max_mem with
          | inl h_orig => 
            exact helper_contains (max acc y) ys orig i' h_bound' h_orig
          | inr h_rest =>
            have result := helper_contains (max acc y) ys orig i' h_bound' (by simp at h_rest; exact h_rest)
            cases result with
            | inl h_orig => left; exact h_orig
            | inr h_rest_mem => right; simp; right; exact h_rest_mem
    have result := helper_contains x xs (x :: xs) i (by rw [scanMax_length]; exact h) (by simp)
    cases result with
    | inl h_orig => 
      simp [List.take]
      exact List.mem_take_of_mem _ h_orig
    | inr h_rest =>
      simp [List.take]
      right
      exact List.mem_take_of_mem _ h_rest

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  constructor
  · exact scanMax_length numbers
  · intro i h
    constructor
    · simp [implementation]
      exact scanMax_contains numbers i h
    · intro j hj
      simp [implementation]
      exact scanMax_monotone numbers j i hj h