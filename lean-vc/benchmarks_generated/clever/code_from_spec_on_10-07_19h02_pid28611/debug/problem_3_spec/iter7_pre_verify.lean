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
def check_prefixes_aux (ops: List Int) (acc: Int) : Bool :=
match ops with
| [] => if acc < 0 then true else false
| x :: xs => 
  let new_acc := acc + x
  if new_acc < 0 then true else check_prefixes_aux xs new_acc

-- LLM HELPER
def check_prefixes (ops: List Int) : Bool :=
match ops with
| [] => false
| x :: xs => if x < 0 then true else check_prefixes_aux xs x

def implementation (operations: List Int) : Bool := check_prefixes operations

-- LLM HELPER
lemma check_prefixes_aux_correct (ops: List Int) (acc: Int) :
  check_prefixes_aux ops acc = true ↔ ∃ i, i ≤ ops.length ∧ (acc :: ops.take i).sum < 0 := by
  constructor
  · intro h
    induction ops generalizing acc with
    | nil => 
      simp [check_prefixes_aux] at h
      use 0
      simp [List.take, List.sum]
      exact ⟨Nat.le_refl 0, h⟩
    | cons x xs ih =>
      simp [check_prefixes_aux] at h
      by_cases hx : acc + x < 0
      · simp [hx] at h
        use 1
        simp [List.take, List.sum]
        exact ⟨Nat.le_add_right 1 xs.length, hx⟩
      · simp [hx] at h
        have := ih (acc + x) h
        obtain ⟨i, hi_le, hi_sum⟩ := this
        use i + 1
        constructor
        · simp [List.length]
          exact Nat.add_le_add_right hi_le 1
        · simp [List.take_succ_cons, List.sum_cons]
          rw [← add_assoc]
          exact hi_sum
  · intro h
    obtain ⟨i, hi_le, hi_sum⟩ := h
    induction ops generalizing acc with
    | nil => 
      simp [List.length] at hi_le
      cases i with
      | zero => 
        simp [List.take, List.sum] at hi_sum
        simp [check_prefixes_aux]
        exact hi_sum
      | succ j => simp at hi_le
    | cons x xs ih =>
      simp [check_prefixes_aux]
      by_cases hx : acc + x < 0
      · exact Or.inl hx
      · simp [hx]
        cases i with
        | zero => 
          simp [List.take, List.sum] at hi_sum
          exfalso
          exact not_le.mpr hi_sum (le_refl _)
        | succ j =>
          apply ih
          constructor
          · simp [List.length] at hi_le
            exact Nat.le_of_succ_le_succ hi_le
          · simp [List.take_succ_cons, List.sum_cons] at hi_sum
            rw [add_assoc] at hi_sum
            exact hi_sum

-- LLM HELPER
lemma check_prefixes_correct (ops: List Int) :
  check_prefixes ops = true ↔ ∃ i, i ≤ ops.length ∧ (ops.take i).sum < 0 := by
  constructor
  · intro h
    cases ops with
    | nil => 
      simp [check_prefixes] at h
    | cons x xs =>
      simp [check_prefixes] at h
      by_cases hx : x < 0
      · simp [hx] at h
        use 1
        simp [List.take, List.sum]
        exact ⟨Nat.le_add_right 1 xs.length, hx⟩
      · simp [hx] at h
        have := check_prefixes_aux_correct xs x
        have := this.mp h
        obtain ⟨i, hi_le, hi_sum⟩ := this
        use i + 1
        constructor
        · simp [List.length]
          exact Nat.add_le_add_right hi_le 1
        · simp [List.take_succ_cons, List.sum_cons]
          rw [← add_assoc]
          exact hi_sum
  · intro h
    obtain ⟨i, hi_le, hi_sum⟩ := h
    cases ops with
    | nil => 
      simp [List.length] at hi_le
      cases i with
      | zero => simp [List.take, List.sum] at hi_sum
      | succ j => simp at hi_le
    | cons x xs =>
      simp [check_prefixes]
      by_cases hx : x < 0
      · exact Or.inl hx
      · simp [hx]
        cases i with
        | zero => simp [List.take, List.sum] at hi_sum
        | succ j =>
          apply (check_prefixes_aux_correct xs x).mpr
          use j
          constructor
          · simp [List.length] at hi_le
            exact Nat.le_of_succ_le_succ hi_le
          · simp [List.take_succ_cons, List.sum_cons] at hi_sum
            rw [add_assoc] at hi_sum
            exact hi_sum

theorem correctness
(operations: List Int)
: problem_spec implementation operations
:= by
  unfold problem_spec implementation
  simp
  use check_prefixes operations
  constructor
  · rfl
  · simp
    rw [check_prefixes_correct]