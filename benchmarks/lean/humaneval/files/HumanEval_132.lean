/- 
function_signature: "def is_nested(string: str) -> Bool"
docstring: |
    Create a function that takes a string as input which contains only parentheses.
    The function should return True if and only if there is a valid subsequence of parentheses
    where at least one parenthesis in the subsequence is nested.
test_cases:
  - input: '(())'
    expected_output: True
  - input: '()))))))((((()'
    expected_output: False
  - input: '()()'
    expected_output: False
  - input: '()'
    expected_output: False
  - input: '(()())'
    expected_output: True
  - input: '(())(('
    expected_output: True
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: string_eq_iff_data_eq
use: |
  Helper function to prove that two strings are equal if their data is equal.
problems: []
sample_problems:
  - 0
-/
def string_eq_iff_data_eq (s1: String) (s2: String)
: s1.data = s2.data ↔ s1 = s2 :=
by
  apply Iff.intro
  intro h
  cases s1
  cases s2
  simp at h
  simp [h]
  intro h
  apply String.data_eq_of_eq
  exact h

/--
name: balanced_paren_non_computable
use: |
  Non-computable definition to check if a string is balanced with respect to parentheses.
problems:
  - 1
  - 6
  - 132
sample_problems:
  - 0
-/
def balanced_paren_non_computable
(paren_string: String) (bracket_type_left : Char) (bracket_type_right: Char): Prop
:=
let chars := paren_string.toList;
(∀ (i : ℕ), i ≤ chars.length → ((chars.take i).count bracket_type_right) ≤ ((chars.take i).count bracket_type_left)) ∧
(chars.count bracket_type_left = chars.count bracket_type_right)

/--
name: count_max_paren_depth_helper
use: |
  Helper to count the maximum depth of parentheses in a string.
problems:
  - 6
  - 132
-/
def count_max_paren_depth_helper
(paren_string: String) (num_open: Int) (max_depth: Nat): Nat :=
-- Recursively count the maximum depth of parentheses
if paren_string.isEmpty then
  max_depth
else
  let c := paren_string.get! 0
  if c == '(' then
    let new_num_open := num_open + 1
    count_max_paren_depth_helper (paren_string.drop 1) (new_num_open) (max_depth.max new_num_open.toNat)
  else if c == ')' then
    count_max_paren_depth_helper (paren_string.drop 1) (num_open - 1) max_depth
  else
    count_max_paren_depth_helper (paren_string.drop 1) num_open max_depth
termination_by paren_string.length
decreasing_by
  all_goals
  {
    rename_i h_non_empty_string
    rw [String.drop_eq, String.length]
    simp
    rw [String.isEmpty_iff] at h_non_empty_string
    by_cases h_paren_nil : paren_string.length ≤ 0
    rw [Nat.le_zero_eq] at h_paren_nil
    rw [←string_eq_iff_data_eq] at h_non_empty_string
    have h_temp : "".data = [] := by simp
    rw [h_temp] at h_non_empty_string
    rw [String.length] at h_paren_nil
    rw [List.length_eq_zero_iff] at h_paren_nil
    contradiction
    have h_temp : paren_string.length > 0 := by linarith
    assumption
  }

/--
name: count_max_paren_depth
use: |
  Function to count the maximum depth of parentheses in a string.
problems:
  - 6
  - 132
-/
def count_max_paren_depth
(paren_string: String): Nat :=
count_max_paren_depth_helper paren_string 0 0

/--
name: is_subsequence
use: |
  Helper to check if List Char xs is a subsequence of List Char ys.
problems:
  - 132
-/
def is_subsequence (xs ys : List Char) : Bool :=
  match xs, ys with
  | [], _ => true
  | _, [] => false
  | x::xs', y::ys' =>
      if x = y then is_subsequence xs' ys' else is_subsequence xs ys'

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: String) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(string: String) :=
-- spec
let spec (result: Bool) :=
string.toList.all (fun x => x = '(' ∨ x = ')') →
result = true ↔
  ∃ x : String,
    is_subsequence x.toList string.toList ∧
    balanced_paren_non_computable x '(' ')' ∧
    2 ≤ count_max_paren_depth x
-- program termination
∃ result, impl string = result ∧
-- return value satisfies spec
spec result

theorem correctness
(string: String)
: problem_spec implementation string :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation "(())" = true
-- #test implementation "()))))))((((()" = false
-- #test implementation "()()" = false
-- #test implementation "()" = false
-- #test implementation "(()())" = true
-- #test implementation "(())((" = true