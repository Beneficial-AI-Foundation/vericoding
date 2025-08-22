import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(brackets: String) :=
-- spec
let spec (result: Bool) :=
  brackets.data.all (fun c => c = '(' ∨ c = ')') →
  (result ↔ balanced_paren_non_computable brackets '(' ')')
-- program terminates
∃ result, impl brackets = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def balanced_paren_non_computable (s: String) (open_char: Char) (close_char: Char) : Bool :=
  let chars := s.data
  let rec helper (chars: List Char) (count: Int) : Bool :=
    match chars with
    | [] => count = 0
    | c :: rest =>
      if c = open_char then
        helper rest (count + 1)
      else if c = close_char then
        if count > 0 then
          helper rest (count - 1)
        else
          false
      else
        helper rest count
  helper chars 0

-- LLM HELPER
def count_balance (chars: List Char) : Int :=
  chars.foldl (fun acc c => 
    if c = '(' then acc + 1
    else if c = ')' then acc - 1
    else acc) 0

-- LLM HELPER
def has_negative_balance (chars: List Char) : Bool :=
  let rec helper (chars: List Char) (count: Int) : Bool :=
    match chars with
    | [] => false
    | c :: rest =>
      let new_count := if c = '(' then count + 1
                      else if c = ')' then count - 1
                      else count
      if new_count < 0 then true
      else helper rest new_count
  helper chars 0

def implementation (paren_string: String) : Bool := 
  let chars := paren_string.data
  decide (count_balance chars = 0) && !has_negative_balance chars

-- LLM HELPER
lemma balanced_paren_non_computable_eq_implementation (s: String) :
  balanced_paren_non_computable s '(' ')' = (decide (count_balance s.data = 0) && !has_negative_balance s.data) := by
  simp [balanced_paren_non_computable, implementation]
  let chars := s.data
  have h : balanced_paren_non_computable.helper '(' ')' chars 0 = (decide (count_balance chars = 0) && !has_negative_balance chars) := by
    induction chars generalizing 0 with
    | nil =>
      simp [balanced_paren_non_computable.helper, count_balance, has_negative_balance]
      simp [has_negative_balance.helper]
      simp [decide_eq_true_iff]
    | cons c rest ih =>
      simp [balanced_paren_non_computable.helper, count_balance, has_negative_balance]
      split_ifs with h1 h2
      · simp [h1, count_balance, has_negative_balance]
        rw [List.foldl_cons]
        simp [h1]
        simp [has_negative_balance.helper]
        simp [h1]
        exact ih 1
      · simp [h2]
        rw [List.foldl_cons]
        simp [h1, h2]
        simp [has_negative_balance.helper]
        simp [h1, h2]
        split_ifs with h3
        · simp [h3, decide_eq_false_iff_not]
          simp [has_negative_balance.helper]
          exact Int.neg_pos.mpr h3
        · simp [h3]
          exact ih (-1)
      · simp [h1, h2]
        rw [List.foldl_cons]
        simp [h1, h2]
        simp [has_negative_balance.helper]
        simp [h1, h2]
        exact ih 0
  exact h

theorem correctness
(brackets: String)
: problem_spec implementation brackets := by
  simp [problem_spec]
  use implementation brackets
  constructor
  · rfl
  · intro h
    rw [balanced_paren_non_computable_eq_implementation]