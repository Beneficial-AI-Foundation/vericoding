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
if paren_string.isEmpty then
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
def separate_groups_helper (chars: List Char) (current_group: List Char) (depth: Nat) (groups: List String) : List String :=
  match chars with
  | [] => 
    if current_group.isEmpty then groups
    else groups ++ [current_group.asString]
  | '(' :: rest =>
    separate_groups_helper rest (current_group ++ ['(']) (depth + 1) groups
  | ')' :: rest =>
    let new_group := current_group ++ [')']
    if depth == 1 then
      separate_groups_helper rest [] 0 (groups ++ [new_group.asString])
    else
      separate_groups_helper rest new_group (depth - 1) groups
  | _ :: rest =>
    separate_groups_helper rest current_group depth groups

def implementation (paren_string: String) : List String :=
  let filtered_chars := paren_string.data.filter (fun c => decide (c = '(') || decide (c = ')'))
  separate_groups_helper filtered_chars [] 0 []

def problem_spec
-- function signature
(impl: String → List String)
-- inputs
(paren_string: String) :=
-- spec
let paren_string_filtered := (paren_string.data.filter (fun c => decide (c = '(') || decide (c = ')'))).asString;
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
lemma separate_groups_concat (chars: List Char) (current_group: List Char) (depth: Nat) (groups: List String) :
  (separate_groups_helper chars current_group depth groups).foldl (· ++ ·) "" = 
  groups.foldl (· ++ ·) "" ++ current_group.asString ++ chars.asString := by
  sorry

-- LLM HELPER
lemma balanced_paren_from_construction (str: String) (h: str ∈ implementation paren_string) :
  balanced_paren_non_computable str '(' ')' := by
  sorry

-- LLM HELPER
lemma count_groups_eq_one (str: String) (h: str ∈ implementation paren_string) :
  count_paren_groups str = 1 := by
  sorry

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string := by
  unfold problem_spec
  use implementation paren_string
  constructor
  · rfl
  · constructor
    · simp [implementation]
      rfl
    · intro str h_in
      constructor
      · exact balanced_paren_from_construction str h_in
      · exact count_groups_eq_one str h_in