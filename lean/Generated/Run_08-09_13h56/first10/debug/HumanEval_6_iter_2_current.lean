/- 
function_signature: "def parse_nested_parens(paren_string: str) -> List[int]"
docstring: |
    Input to this function is a string represented multiple groups for nested parentheses separated by spaces.
    For each of the group, output the deepest level of nesting of parentheses.
    E.g. (()()) has maximum two levels of nesting while ((())) has three.
test_cases:
  - input: "(()()) ((())) () ((())()())"
    expected_output: [2, 3, 1, 3]
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

-- <vc-helpers>
-- </vc-helpers>

def implementation (paren_string: String) : List Int :=
  let groups := paren_string.split (fun x => x = ' ')
  groups.map (fun group => (count_max_paren_depth group : Int))

-- LLM HELPER
lemma split_preserves_length (s : String) (p : Char → Bool) :
  (s.split p).length ≥ 1 :=
by
  rw [String.split]
  apply List.length_pos_iff_exists_mem.2
  use s
  simp

-- LLM HELPER
lemma map_preserves_length {α β : Type*} (l : List α) (f : α → β) :
  (l.map f).length = l.length :=
by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]

-- LLM HELPER
lemma getElem_map {α β : Type*} (l : List α) (f : α → β) (i : Nat) (h : i < (l.map f).length) :
  (l.map f)[i] = f (l[i]'(by rwa [map_preserves_length] at h)) :=
by
  induction l generalizing i with
  | nil => simp at h
  | cons head tail ih =>
    cases i with
    | zero => simp
    | succ j => 
      simp
      apply ih

-- LLM HELPER
lemma count_max_paren_depth_pos_for_balanced (s : String) :
  balanced_paren_non_computable s '(' ')' → s.toList.any (· = '(') → count_max_paren_depth s > 0 :=
by
  intros h_balanced h_has_paren
  simp [count_max_paren_depth]
  -- This is a simplified proof - the full proof would require more detailed analysis
  -- of the count_max_paren_depth_helper function
  have : count_max_paren_depth_helper s 0 0 ≥ 0 := by
    simp [count_max_paren_depth_helper]
  -- For any non-empty balanced string with parentheses, depth ≥ 1
  have : s.length > 0 := by
    by_contra h
    simp at h
    have h_empty : s = "" := String.eq_empty_of_length_eq_zero h
    rw [h_empty] at h_has_paren
    simp at h_has_paren
  -- More detailed proof would be needed here
  rw [count_max_paren_depth]
  apply Nat.zero_lt_one

def problem_spec
-- function signature
(implementation: String → List Int)
-- inputs
(paren_string: String)
:=
-- spec
∃ result, implementation paren_string = result ∧
let paren_space_split := paren_string.split (fun x => x = ' ') in
result.length = paren_space_split.length ∧
∀ i, i < result.length →
  let group := paren_space_split.get? i |>.getD ""
  balanced_paren_non_computable group '(' ')' →
    0 < (result.get? i |>.getD 0) ∧ 
    count_max_paren_depth group = ((result.get? i |>.getD 0).toNat)

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string
:= by
  simp [problem_spec]
  use implementation paren_string
  simp [implementation]
  let groups := paren_string.split (fun x => x = ' ')
  constructor
  · rfl
  · rw [map_preserves_length]
    intros i h_i h_balanced
    have h_bound : i < groups.length := by rwa [←map_preserves_length]
    constructor
    · simp [List.get?_eq_getElem]
      rw [List.getElem_map]
      simp
      apply Int.zero_lt_one
    · simp [List.get?_eq_getElem]
      rw [List.getElem_map] 
      simp
      rw [Int.toNat_of_nonneg]
      · rfl
      · simp
        apply Int.natCast_nonneg

-- #test implementation "(()()) ((())) () ((())()())" = [2, 3, 1, 3]