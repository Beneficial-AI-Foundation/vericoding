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
  simp [balanced_paren_non_computable, count_balance, has_negative_balance]
  induction s.data with
  | nil => simp [balanced_paren_non_computable]
  | cons c rest ih =>
    simp [balanced_paren_non_computable]
    split_ifs <;> simp [*]

theorem correctness
(brackets: String)
: problem_spec implementation brackets := by
  simp [problem_spec]
  use implementation brackets
  constructor
  · rfl
  · intro h
    rw [balanced_paren_non_computable_eq_implementation]