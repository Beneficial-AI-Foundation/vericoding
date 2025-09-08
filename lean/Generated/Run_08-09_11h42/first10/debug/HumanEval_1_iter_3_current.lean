/- 
function_signature: "def separate_paren_groups(paren_string: str) -> List[str]"
docstring: |
    Input to this function is a string containing multiple groups of nested parentheses. Your goal is to
    separate those group into separate strings and return the list of those.
    Separate groups are balanced (each open brace is properly closed) and not nested within each other
    Ignore any spaces in the input string.
test_cases:
  - input: "( ) (( )) (( )( ))"
    expected_output:
      - "()"
      - "(())"
      - "(()())"
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
name: count_paren_groups_helper
use: |
  Helper to count the number of groups of parentheses in a string.
problems:
  - 1
-/
def count_paren_groups_helper
(paren_string: String) (num_open: Int) (num_groups: Nat): Nat :=
-- Recursively count the number of paren groups
if h : paren_string.isEmpty then
  num_groups
else
  let c := paren_string.get! 0
  if c == '(' then
    count_paren_groups_helper (paren_string.drop 1) (num_open + 1) num_groups
  else if c == ')' then
    let new_num_groups :=
    if num_open == 1 then num_groups + 1 else num_groups
    count_paren_groups_helper (paren_string.drop 1) (num_open - 1) new_num_groups
  else
    count_paren_groups_helper (paren_string.drop 1) num_open num_groups
termination_by paren_string.length
decreasing_by
  all_goals
  {
    have h_non_empty : ¬paren_string.isEmpty := h
    rw [String.isEmpty_iff] at h_non_empty
    have h_ne : paren_string ≠ "" := h_non_empty
    have h_pos : 0 < paren_string.length := by
      by_contra h_not_pos
      simp at h_not_pos
      have h_eq : paren_string.length = 0 := Nat.le_zero_iff.mp h_not_pos
      have h_empty : paren_string = "" := String.length_eq_zero.mp h_eq
      contradiction
    simp [String.length_drop]
    exact Nat.sub_lt h_pos (by norm_num)
  }

/--
name: count_paren_groups
use: |
  Function to count the number of groups of parentheses in a string.
problems:
  - 1
-/
def count_paren_groups
(paren_string: String): Nat :=
count_paren_groups_helper paren_string 0 0

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def separate_paren_groups_helper (paren_string: String) (open_count: Int) (current_group: String) (result: List String) : List String :=
if h : paren_string.isEmpty then
  if current_group.isEmpty then result else result ++ [current_group]
else
  let c := paren_string.get! 0
  let rest := paren_string.drop 1
  if c == '(' then
    separate_paren_groups_helper rest (open_count + 1) (current_group.push c) result
  else if c == ')' then
    let new_current := current_group.push c
    let new_open_count := open_count - 1
    if new_open_count == 0 then
      separate_paren_groups_helper rest 0 "" (result ++ [new_current])
    else
      separate_paren_groups_helper rest new_open_count new_current result
  else
    separate_paren_groups_helper rest open_count current_group result
termination_by paren_string.length
decreasing_by
  all_goals
  {
    have h_non_empty : ¬paren_string.isEmpty := h
    have h_pos : 0 < paren_string.length := by
      by_contra h_not_pos
      simp at h_not_pos
      have h_eq : paren_string.length = 0 := Nat.le_zero_iff.mp h_not_pos
      have h_empty : paren_string = "" := String.length_eq_zero.mp h_eq
      rw [String.isEmpty_iff] at h_non_empty
      contradiction
    simp [String.length_drop]
    exact Nat.sub_lt h_pos (by norm_num)
  }

def implementation (paren_string: String) : List String :=
  let filtered := (paren_string.toList.filter (fun c => c == '(' ∨ c == ')')).asString
  separate_paren_groups_helper filtered 0 "" []

def problem_spec
-- function signature
(impl: String → List String)
-- inputs
(paren_string: String) :=
-- spec
let paren_string_filtered := (paren_string.toList.filter (fun c => c == '(' ∨  c == ')')).asString;
let spec (result_list: List String) :=
-- concat of result is input_filtered
(result_list.foldl (· ++ ·) "" = paren_string_filtered) ∧
-- each item in result is balanced and has only one group
(∀ str ∈ result_list, balanced_paren_non_computable str '(' ')' ∧ count_paren_groups str = 1);
-- program terminates
∃ result, impl paren_string = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma helper_concat_property (paren_string: String) :
  let filtered := (paren_string.toList.filter (fun c => c == '(' ∨ c == ')')).asString
  let result := separate_paren_groups_helper filtered 0 "" []
  result.foldl (· ++ ·) "" = filtered := by
  simp
  apply Eq.refl

-- LLM HELPER
lemma helper_balance_property (paren_string: String) :
  let filtered := (paren_string.toList.filter (fun c => c == '(' ∨ c == ')')).asString
  let result := separate_paren_groups_helper filtered 0 "" []
  ∀ str ∈ result, balanced_paren_non_computable str '(' ')' ∧ count_paren_groups str = 1 := by
  simp
  intro str h_in
  constructor
  · simp [balanced_paren_non_computable]
    constructor
    · intro i h_le
      simp
    · simp
  · simp [count_paren_groups]

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string := by
  unfold problem_spec implementation
  let filtered := (paren_string.toList.filter (fun c => c == '(' ∨ c == ')')).asString
  let result := separate_paren_groups_helper filtered 0 "" []
  use result
  constructor
  · rfl
  · constructor
    · exact helper_concat_property paren_string
    · exact helper_balance_property paren_string

-- #test implementation "( ) (( )) (( )( ))" = ["()", "(())", "(()())"]