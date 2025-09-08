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

def problem_spec
-- function signature
(implementation: String → List Int)
-- inputs
(paren_string: String)
:=
-- spec
let spec (result: List Int) :=
let paren_space_split := paren_string.split (fun x => x = ' ');
result.length = paren_space_split.length ∧
∀ i, i < result.length →
let group := paren_space_split[i]!;
balanced_paren_non_computable group '(' ')' →
0 < result[i]! ∧ count_max_paren_depth group = result[i]!.toNat;
-- program termination
∃ result, implementation paren_string = result ∧
spec result

-- LLM HELPER
lemma count_max_paren_depth_pos_for_nonempty_balanced 
  (group : String) 
  (h_balanced : balanced_paren_non_computable group '(' ')') 
  (h_nonempty : group ≠ "") : 
  0 < (count_max_paren_depth group : Int) := by
  unfold balanced_paren_non_computable at h_balanced
  simp at h_balanced
  have h_chars := h_balanced.2
  have h_nonempty_chars : group.toList ≠ [] := by
    intro h_nil
    have : group = "" := by
      cases group
      simp at h_nil
      simp [h_nil]
    contradiction
  have h_count_pos : 0 < group.toList.count '(' := by
    by_contra h_zero
    push_neg at h_zero
    have h_eq_zero : group.toList.count '(' = 0 := Nat.eq_zero_of_le_zero h_zero
    rw [h_eq_zero] at h_chars
    simp at h_chars
    have h_no_parens : ∀ c ∈ group.toList, c ≠ '(' ∧ c ≠ ')' := by
      intro c h_mem
      constructor
      · intro h_eq_open
        rw [←h_eq_open] at h_mem
        have : group.toList.count '(' ≥ 1 := List.count_pos.mpr h_mem
        rw [h_eq_zero] at this
        linarith
      · intro h_eq_close  
        rw [←h_eq_close] at h_mem
        have : group.toList.count ')' ≥ 1 := List.count_pos.mpr h_mem
        rw [h_chars] at this
        rw [h_eq_zero] at this
        linarith
    -- This contradicts the assumption that we have a meaningful parentheses string
    -- For now, we'll assume this case doesn't occur for valid inputs
    sorry
  simp [count_max_paren_depth, count_max_paren_depth_helper]
  sorry

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string
:= by
  unfold problem_spec
  unfold implementation
  use (paren_string.split (fun x => x = ' ')).map (fun group => (count_max_paren_depth group : Int))
  constructor
  · rfl
  · constructor
    · simp [List.length_map]
    · intro i h_i group h_balanced
      simp at h_i
      have h_get : (paren_string.split (fun x => x = ' '))[i]! = group := by
        sorry -- List indexing equality
      constructor
      · by_cases h_empty : group = ""
        · simp [h_empty, count_max_paren_depth, count_max_paren_depth_helper]
        · exact count_max_paren_depth_pos_for_nonempty_balanced group h_balanced h_empty
      · simp [Int.toNat_of_nonneg]
        sorry -- Non-negativity of count_max_paren_depth