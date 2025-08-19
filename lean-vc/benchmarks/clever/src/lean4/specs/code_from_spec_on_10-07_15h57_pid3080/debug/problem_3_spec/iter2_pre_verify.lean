import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def check_below_zero_aux (ops: List Int) (acc: Int) : Bool :=
  match ops with
  | [] => false
  | x :: xs => 
    let new_acc := acc + x
    if new_acc < 0 then true
    else check_below_zero_aux xs new_acc

def implementation (operations: List Int) : Bool := check_below_zero_aux operations 0

-- LLM HELPER
lemma take_sum_eq_prefix_sum (ops: List Int) (i: Nat) (acc: Int) :
  i ≤ ops.length →
  (ops.take i).sum = (ops.take i).foldl (· + ·) 0 := by
  intro h
  rw [List.sum_eq_foldl]

-- LLM HELPER
lemma check_below_zero_aux_correct (ops: List Int) (acc: Int) :
  check_below_zero_aux ops acc = true ↔ 
  ∃ i, i ≤ ops.length ∧ i > 0 ∧ acc + (ops.take i).sum < 0 := by
  induction ops generalizing acc with
  | nil => 
    simp [check_below_zero_aux]
  | cons x xs ih =>
    simp [check_below_zero_aux]
    constructor
    · intro h
      by_cases h_neg : acc + x < 0
      · use 1
        simp [h_neg, List.take_one, List.sum_cons, List.sum_nil]
      · simp [h_neg] at h
        obtain ⟨i, hi_len, hi_pos, hi_sum⟩ := (ih (acc + x)).mp h
        use i + 1
        constructor
        · simp [hi_len]
        constructor
        · omega
        · have : (x :: xs).take (i + 1) = x :: xs.take i := by
            rw [List.take_succ_cons]
          rw [this, List.sum_cons]
          exact hi_sum
    · intro ⟨i, hi_len, hi_pos, hi_sum⟩
      by_cases h_neg : acc + x < 0
      · exact h_neg
      · simp [h_neg]
        apply (ih (acc + x)).mpr
        cases i with
        | zero => omega
        | succ j =>
          use j
          constructor
          · simp at hi_len
            exact hi_len
          constructor
          · omega
          · have : (x :: xs).take (j + 1) = x :: xs.take j := by
              rw [List.take_succ_cons]
            rw [this, List.sum_cons] at hi_sum
            exact hi_sum

-- LLM HELPER
lemma implementation_correct_aux (ops: List Int) :
  implementation ops = true ↔ 
  ∃ i, i ≤ ops.length ∧ i > 0 ∧ (ops.take i).sum < 0 := by
  simp [implementation]
  rw [check_below_zero_aux_correct]
  simp

-- LLM HELPER
lemma zero_take_sum (ops: List Int) : (ops.take 0).sum = 0 := by
  simp [List.take_zero, List.sum_nil]

theorem correctness
(operations: List Int)
: problem_spec implementation operations := by
  unfold problem_spec
  use implementation operations
  constructor
  · rfl
  · simp
    by_cases h : implementation operations = true
    · simp [h]
      rw [implementation_correct_aux] at h
      obtain ⟨i, hi_len, hi_pos, hi_sum⟩ := h
      use i
      exact ⟨hi_len, hi_sum⟩
    · simp [h]
      intro i hi_len hi_sum
      have : implementation operations = true := by
        rw [implementation_correct_aux]
        by_cases h_zero : i = 0
        · rw [h_zero] at hi_sum
          rw [zero_take_sum] at hi_sum
          omega
        · use i
          exact ⟨hi_len, Nat.pos_of_ne_zero h_zero, hi_sum⟩
      exact h this