def problem_spec
-- function signature
(impl: List Int → Bool)
-- inputs
(operations: List Int) :=
-- spec
let below_zero_condition := ∃ i, i ≤ operations.length ∧
(operations.take i).sum < 0;
let spec (result: Bool) :=
if result then below_zero_condition else ¬below_zero_condition;
-- program terminates
∃ result, impl operations = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def check_below_zero (ops: List Int) : Bool :=
  let rec aux (remaining: List Int) (current_sum: Int) : Bool :=
    match remaining with
    | [] => false
    | x :: xs => 
      let new_sum := current_sum + x
      if new_sum < 0 then true
      else aux xs new_sum
  aux ops 0

def implementation (operations: List Int) : Bool := check_below_zero operations

-- LLM HELPER
lemma check_below_zero_correct (ops: List Int) :
  check_below_zero ops = true ↔ ∃ i, i ≤ ops.length ∧ (ops.take i).sum < 0 := by
  constructor
  · intro h
    induction ops with
    | nil => 
      simp [check_below_zero] at h
    | cons x xs ih =>
      simp [check_below_zero] at h
      by_cases h_case : x < 0
      · use 1
        simp [List.take, List.sum]
        exact h_case
      · have h_nonneg : x ≥ 0 := le_of_not_gt h_case
        have h_recursive : check_below_zero.aux xs x = true := by
          simp [check_below_zero] at h
          by_cases h_sum : x < 0
          · contradiction
          · exact h
        have ⟨i, hi_le, hi_sum⟩ := ih.mp h_recursive
        use i + 1
        constructor
        · simp
          exact Nat.succ_le_succ hi_le
        · simp [List.take, List.sum]
          exact hi_sum
  · intro ⟨i, hi_le, hi_sum⟩
    induction ops generalizing i with
    | nil => 
      simp at hi_le hi_sum
    | cons x xs ih =>
      simp [check_below_zero]
      by_cases h_case : x < 0
      · exact h_case
      · have h_nonneg : x ≥ 0 := le_of_not_gt h_case
        cases' i with i'
        · simp [List.take, List.sum] at hi_sum
        · have hi_sum' : (xs.take i').sum < 0 := by
            simp [List.take, List.sum] at hi_sum
            linarith
          have hi_le' : i' ≤ xs.length := by
            simp at hi_le
            exact Nat.le_of_succ_le_succ hi_le
          exact ih i' hi_le' hi_sum'

-- LLM HELPER
lemma check_below_zero_false (ops: List Int) :
  check_below_zero ops = false ↔ ¬∃ i, i ≤ ops.length ∧ (ops.take i).sum < 0 := by
  constructor
  · intro h h_exists
    have h_true := (check_below_zero_correct ops).mpr h_exists
    rw [h] at h_true
    exact Bool.noConfusion h_true
  · intro h_not_exists
    by_contra h_contra
    have h_true : check_below_zero ops = true := by
      cases' check_below_zero ops with
      | false => contradiction
      | true => rfl
    have h_exists := (check_below_zero_correct ops).mp h_true
    exact h_not_exists h_exists

theorem correctness
(operations: List Int)
: problem_spec implementation operations := by
  use check_below_zero operations
  constructor
  · rfl
  · simp [problem_spec]
    by_cases h : check_below_zero operations = true
    · simp [h]
      exact (check_below_zero_correct operations).mp h
    · simp [h]
      have h_false : check_below_zero operations = false := by
        cases' check_below_zero operations with
        | false => rfl
        | true => contradiction
      exact (check_below_zero_false operations).mp h_false