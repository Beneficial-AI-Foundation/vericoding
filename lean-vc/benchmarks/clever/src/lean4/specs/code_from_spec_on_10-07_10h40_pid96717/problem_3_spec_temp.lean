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
def goes_below_zero_aux (ops: List Int) (acc: Int) : Bool :=
  match ops with
  | [] => false
  | x :: xs => 
    let new_acc := acc + x
    if new_acc < 0 then true
    else goes_below_zero_aux xs new_acc

def implementation (operations: List Int) : Bool := goes_below_zero_aux operations 0

-- LLM HELPER
lemma goes_below_zero_aux_correct (ops: List Int) (acc: Int) :
  goes_below_zero_aux ops acc = true ↔ 
  ∃ i, i ≤ ops.length ∧ acc + (ops.take i).sum < 0 := by
  induction ops generalizing acc with
  | nil => 
    simp [goes_below_zero_aux]
    constructor
    · intro h
      cases h
    · intro ⟨i, hi, hsum⟩
      cases i with
      | zero => 
        simp at hsum
        linarith
      | succ j =>
        simp at hi
  | cons x xs ih =>
    simp [goes_below_zero_aux]
    by_cases h : acc + x < 0
    · simp [h]
      use 1
      simp [List.take]
      exact h
    · simp [h]
      rw [ih]
      constructor
      · intro ⟨i, hi, hsum⟩
        use i + 1
        constructor
        · simp
          exact Nat.succ_le_succ hi
        · simp [List.take]
          cases i with
          | zero =>
            simp at hsum
            exact hsum
          | succ j =>
            rw [List.take_succ]
            rw [List.sum_cons]
            exact hsum
      · intro ⟨i, hi, hsum⟩
        cases i with
        | zero =>
          simp at hsum
          linarith
        | succ j =>
          use j
          constructor
          · simp at hi
            exact Nat.le_of_succ_le_succ hi
          · rw [List.take_succ] at hsum
            rw [List.sum_cons] at hsum
            exact hsum

theorem correctness
(operations: List Int)
: problem_spec implementation operations := by
  unfold problem_spec implementation
  use goes_below_zero_aux operations 0
  constructor
  · rfl
  · simp
    rw [goes_below_zero_aux_correct]
    simp [add_zero]
    constructor
    · intro h
      exact h
    · intro h
      exact h