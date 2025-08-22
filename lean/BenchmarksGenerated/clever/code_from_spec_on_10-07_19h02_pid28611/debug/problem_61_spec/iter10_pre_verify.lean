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
lemma count_balance_nil : count_balance [] = 0 := by
  simp [count_balance]

-- LLM HELPER
lemma has_negative_balance_nil : has_negative_balance [] = false := by
  simp [has_negative_balance]

-- LLM HELPER
lemma count_balance_cons (c : Char) (rest : List Char) :
  count_balance (c :: rest) = 
  (if c = '(' then 1 else if c = ')' then -1 else 0) + count_balance rest := by
  simp [count_balance]
  rw [List.foldl_cons]
  simp [count_balance]

-- LLM HELPER
lemma has_negative_balance_cons (c : Char) (rest : List Char) (count : Int) :
  has_negative_balance.helper (c :: rest) count = 
  let new_count := if c = '(' then count + 1 else if c = ')' then count - 1 else count
  decide (new_count < 0) || has_negative_balance.helper rest new_count := by
  simp [has_negative_balance.helper]
  split_ifs <;> simp

-- LLM HELPER
lemma balanced_paren_non_computable_eq_implementation (s: String) :
  balanced_paren_non_computable s '(' ')' = (decide (count_balance s.data = 0) && !has_negative_balance s.data) := by
  simp [balanced_paren_non_computable, implementation]
  let chars := s.data
  suffices h : balanced_paren_non_computable.helper '(' ')' chars 0 = 
    (!has_negative_balance.helper chars 0 && decide (count_balance chars = 0)) by
    exact h
  let rec helper_eq (chars: List Char) (count: Int) : 
    balanced_paren_non_computable.helper '(' ')' chars count = 
    (!decide (count < 0) && !has_negative_balance.helper chars count && decide (count + count_balance chars = 0)) := by
    match chars with
    | [] => 
      simp [balanced_paren_non_computable.helper, has_negative_balance.helper, count_balance_nil]
    | c :: rest =>
      simp [balanced_paren_non_computable.helper, has_negative_balance.helper]
      rw [count_balance_cons]
      split_ifs with h1 h2
      · simp [h1]
        rw [helper_eq]
        simp [Int.add_assoc]
      · simp [h1, h2]
        split_ifs with h3
        · rw [helper_eq]
          simp [Int.add_sub_cancel, Int.sub_add_cancel]
        · simp
      · simp [h1, h2]
        rw [helper_eq]
        simp [Int.add_zero]
  rw [helper_eq]
  simp [Int.zero_add]

theorem correctness
(brackets: String)
: problem_spec implementation brackets := by
  simp [problem_spec]
  use implementation brackets
  constructor
  · rfl
  · intro h
    rw [balanced_paren_non_computable_eq_implementation]