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
def check_below_zero_aux (ops: List Int) (current_sum: Int) : Bool :=
  match ops with
  | [] => false
  | x :: xs =>
    let new_sum := current_sum + x
    if new_sum < 0 then true
    else check_below_zero_aux xs new_sum

-- LLM HELPER
def check_below_zero (ops: List Int) : Bool :=
  match ops with
  | [] => false
  | x :: xs => 
    let sum := x
    if sum < 0 then true
    else check_below_zero_aux xs sum

def implementation (operations: List Int) : Bool := check_below_zero operations

-- LLM HELPER
lemma check_below_zero_aux_correct (ops: List Int) (current_sum: Int) :
  check_below_zero_aux ops current_sum = true ↔ 
  ∃ i, i ≤ ops.length ∧ (current_sum + (ops.take i).sum) < 0 := by
  constructor
  · intro h
    induction ops generalizing current_sum with
    | nil => 
      simp [check_below_zero_aux] at h
    | cons x xs ih =>
      simp [check_below_zero_aux] at h
      let new_sum := current_sum + x
      if h_neg : new_sum < 0 then
        use 1
        simp [List.take, List.sum]
        exact h_neg
      else
        simp [h_neg] at h
        have := ih new_sum h
        obtain ⟨i, hi_le, hi_sum⟩ := this
        use i + 1
        constructor
        · simp
          exact Nat.succ_le_succ hi_le
        · simp [List.take, List.sum_cons]
          convert hi_sum
          ring
  · intro ⟨i, hi_le, hi_sum⟩
    induction ops generalizing current_sum with
    | nil => 
      simp at hi_le
      simp [List.take, List.sum] at hi_sum
      simp [check_below_zero_aux]
    | cons x xs ih =>
      simp [check_below_zero_aux]
      let new_sum := current_sum + x
      cases' i with i
      · simp [List.take, List.sum] at hi_sum
        exact hi_sum
      · simp [List.take, List.sum_cons] at hi_sum
        if h_neg : new_sum < 0 then
          exact h_neg
        else
          simp [h_neg]
          apply ih
          use i
          constructor
          · simp at hi_le
            exact Nat.le_of_succ_le_succ hi_le
          · convert hi_sum
            ring

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
      if h_neg : x < 0 then
        use 1
        simp [List.take, List.sum]
        exact h_neg
      else
        simp [h_neg] at h
        have aux_correct := check_below_zero_aux_correct xs x
        rw [aux_correct] at h
        obtain ⟨i, hi_le, hi_sum⟩ := h
        use i + 1
        constructor
        · simp
          exact Nat.succ_le_succ hi_le
        · simp [List.take, List.sum]
          convert hi_sum
          rw [List.take_succ_cons]
          simp [List.sum_cons]
  · intro ⟨i, hi_le, hi_sum⟩
    induction ops with
    | nil => 
      simp at hi_le
      simp [List.take] at hi_sum
      simp [List.sum] at hi_sum
    | cons x xs ih =>
      simp [check_below_zero]
      cases' i with i
      · simp [List.take, List.sum] at hi_sum
      · simp [List.take] at hi_sum
        simp [List.sum_cons] at hi_sum
        if h_neg : x < 0 then
          exact h_neg
        else
          simp [h_neg]
          have aux_correct := check_below_zero_aux_correct xs x
          rw [aux_correct]
          use i
          constructor
          · simp at hi_le
            exact Nat.le_of_succ_le_succ hi_le
          · convert hi_sum
            rw [List.take_succ_cons] at hi_sum
            simp [List.sum_cons] at hi_sum
            exact hi_sum

-- LLM HELPER
lemma check_below_zero_false_correct (ops: List Int) :
  check_below_zero ops = false ↔ ¬∃ i, i ≤ ops.length ∧ (ops.take i).sum < 0 := by
  constructor
  · intro h
    intro ⟨i, hi_le, hi_sum⟩
    have := check_below_zero_correct ops
    rw [this] at h
    simp at h
    exact h ⟨i, hi_le, hi_sum⟩
  · intro h
    have := check_below_zero_correct ops
    cases' h_dec : check_below_zero ops with
    | false => rfl
    | true => 
      rw [this] at h_dec
      exact False.elim (h h_dec)

theorem correctness
(operations: List Int)
: problem_spec implementation operations := by
  simp [problem_spec, implementation]
  use check_below_zero operations
  constructor
  · rfl
  · simp
    cases' h : check_below_zero operations with
    | false =>
      simp [h]
      exact (check_below_zero_false_correct operations).mp h
    | true =>
      simp [h]
      exact (check_below_zero_correct operations).mp h