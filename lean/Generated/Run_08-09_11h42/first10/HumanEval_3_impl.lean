/- 
function_signature: "def below_zero(operations: List[int]) -> bool"
docstring: |
    You're given a list of deposit and withdrawal operations on a bank account that starts with
    zero balance. Your task is to detect if at any point the balance of account fallls below zero, and
    at that point function should return True. Otherwise it should return False.
test_cases:
  - input:
      - 1
      - 2
      - 3
    expected_output: false
  - input:
      - 1
      - 2
      - -4
      - 5
    expected_output: true
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (operations: List Int) : Bool :=
  let rec check_prefixes (ops : List Int) (current_sum : Int) : Bool :=
    match ops with
    | [] => false
    | head :: tail => 
      let new_sum := current_sum + head
      if new_sum < 0 then true
      else check_prefixes tail new_sum
  check_prefixes operations 0

-- LLM HELPER
def below_zero_condition (operations: List Int) : Prop := 
  ∃ i, i ≤ operations.length ∧ (operations.take i).sum < 0

def problem_spec
-- function signature
(impl: List Int → Bool)
-- inputs
(operations: List Int) :=
-- spec
let spec (result: Bool) :=
if result then below_zero_condition operations else ¬below_zero_condition operations;
-- program terminates
∃ result, impl operations = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma sum_take_succ (l : List Int) (n : Nat) (h : n < l.length) :
  (l.take (n + 1)).sum = (l.take n).sum + l[n] := by
  rw [← List.take_concat_get h]
  rw [List.sum_concat]

-- LLM HELPER
def check_prefixes (ops : List Int) (current_sum : Int) : Bool :=
  match ops with
  | [] => false
  | head :: tail => 
    let new_sum := current_sum + head
    if new_sum < 0 then true
    else check_prefixes tail new_sum

-- LLM HELPER
lemma check_prefixes_correct (ops : List Int) (start_sum : Int) :
  check_prefixes ops start_sum = true ↔ 
  ∃ k, k < ops.length ∧ start_sum + (ops.take (k + 1)).sum < 0 := by
  induction ops generalizing start_sum with
  | nil => 
    simp [check_prefixes]
  | cons head tail ih =>
    simp only [check_prefixes]
    by_cases h : start_sum + head < 0
    · simp [h]
      constructor
      · intro _
        use 0
        simp [List.take, List.sum_cons, List.sum_nil]
        exact h
      · intro _
        trivial
    · simp [h]
      rw [ih]
      constructor
      · intro ⟨k, hk, hsum⟩
        use k + 1
        constructor
        · simp [List.length_cons]
          omega
        · rw [List.take_cons, List.sum_cons]
          rw [add_comm start_sum head, add_assoc]
          exact hsum
      · intro ⟨k, hk, hsum⟩
        cases k with
        | zero =>
          rw [List.take_cons, List.take_zero, List.sum_nil, add_zero] at hsum
          contradiction
        | succ k' =>
          use k'
          constructor
          · simp [List.length_cons] at hk
            omega
          · rw [List.take_cons, List.sum_cons] at hsum
            rw [add_comm start_sum head, add_assoc] at hsum
            exact hsum

-- LLM HELPER
lemma take_length_eq (l : List Int) (i : Nat) (h : i ≤ l.length) :
  (l.take i).length = i := by
  exact List.length_take_of_le h

theorem correctness
(operations: List Int)
: problem_spec implementation operations
:= by
  unfold problem_spec implementation
  use implementation operations
  constructor
  · rfl
  · simp only [implementation]
    by_cases h : check_prefixes operations 0 = true
    · simp [h]
      unfold below_zero_condition
      rw [check_prefixes_correct] at h
      obtain ⟨k, hk, hsum⟩ := h
      use k + 1
      constructor
      · omega
      · rw [← zero_add (operations.take (k + 1)).sum]
        exact hsum
    · simp [h]
      unfold below_zero_condition
      push_neg
      intro i hi
      have : ¬(∃ k, k < operations.length ∧ 0 + (operations.take (k + 1)).sum < 0) := by
        rw [← check_prefixes_correct]
        exact h
      push_neg at this
      by_cases hi0 : i = 0
      · simp [hi0, List.take, List.sum_nil]
      · have hi_pos : i > 0 := Nat.pos_of_ne_zero hi0
        by_contra h_neg
        have hilt : i ≤ operations.length := hi
        by_cases heq : i = operations.length
        · rw [heq] at h_neg
          rw [List.take_length] at h_neg
          have : operations.length - 1 < operations.length := by
            cases operations with
            | nil => 
              rw [heq] at hi_pos
              simp at hi_pos
            | cons _ _ =>
              rw [List.length_cons]
              omega
          have hneg := this (operations.length - 1) this
          simp at hneg
          have : operations.length - 1 + 1 = operations.length := by omega
          rw [this, List.take_length] at hneg
          exact hneg h_neg
        · have : i < operations.length := Nat.lt_of_le_of_ne hilt heq
          have : i - 1 < operations.length := by omega
          have hneg := this (i - 1) this
          simp at hneg
          have : i - 1 + 1 = i := by omega
          rw [this] at hneg
          exact hneg h_neg