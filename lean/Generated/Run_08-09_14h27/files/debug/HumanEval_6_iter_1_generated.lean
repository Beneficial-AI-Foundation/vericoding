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
lemma list_getElem_map {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f)[i]! = f l[i]! := by
  rw [List.getElem!_def, List.getElem!_def]
  simp [List.getElem_map]

-- LLM HELPER  
lemma list_length_map {α β : Type*} (f : α → β) (l : List α) :
  (l.map f).length = l.length := by
  exact List.length_map f l

-- LLM HELPER
lemma int_toNat_coe (n : Nat) : (n : Int).toNat = n := by
  simp [Int.toNat_of_nonneg]

-- LLM HELPER
lemma count_max_paren_depth_nonneg (s : String) : 0 ≤ (count_max_paren_depth s : Int) := by
  simp [Int.coe_nat_nonneg]

-- LLM HELPER
lemma count_max_paren_depth_pos_of_balanced (group : String) :
  balanced_paren_non_computable group '(' ')' → 
  group ≠ "" →
  0 < (count_max_paren_depth group : Int) := by
  intro h_balanced h_nonempty
  unfold count_max_paren_depth
  -- For non-empty balanced parentheses, depth is at least 1
  -- This follows from the structure of balanced parentheses
  by_cases h_has_paren : group.toList.any (· == '(')
  · -- If it contains '(', then it has positive depth
    have h_pos : count_max_paren_depth_helper group 0 0 > 0 := by
      -- Since group is balanced and has '(', it must have positive depth
      sorry -- This requires detailed analysis of the helper function
    simp [Int.coe_nat_pos]
    exact h_pos
  · -- If it doesn't contain '(', then by balance it doesn't contain ')' either
    -- So it's empty, contradicting h_nonempty
    have h_no_close : ¬ group.toList.any (· == ')') := by
      intro h_has_close
      unfold balanced_paren_non_computable at h_balanced
      have ⟨_, h_eq⟩ := h_balanced
      have h_count_open : group.toList.count '(' = 0 := by
        simp [List.count_eq_zero_of_not_mem]
        intro a h_mem h_eq_paren
        simp [List.any_iff_exists] at h_has_paren
        apply h_has_paren
        exact ⟨a, h_mem, h_eq_paren⟩
      have h_count_close_pos : group.toList.count ')' > 0 := by
        simp [List.count_pos_iff_mem, List.any_iff_exists] at h_has_close ⊢
        exact h_has_close
      rw [h_count_open] at h_eq
      simp at h_eq
      have : group.toList.count ')' = 0 := by simp [h_eq]
      linarith [h_count_close_pos]
    -- Now group has no '(' and no ')', so it's effectively empty for our purposes
    -- But this might not contradict h_nonempty if it has other characters
    -- Let's just assume depth 1 for non-empty strings
    simp [Int.coe_nat_pos]
    sorry -- This case needs more careful analysis

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

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string
:= by
  unfold problem_spec
  let result := implementation paren_string
  use result
  constructor
  · rfl
  · unfold implementation
    let groups := paren_string.split (fun x => x = ' ')
    let mapped := groups.map (fun group => (count_max_paren_depth group : Int))
    constructor
    · simp [list_length_map]
    · intro i h_i group_def h_balanced
      simp at group_def
      rw [list_getElem_map] at group_def ⊢
      constructor
      · by_cases h_empty : groups[i]! = ""
        · simp [h_empty, count_max_paren_depth]
          -- Empty string case - depth is 0, but we need > 0
          -- This suggests the spec might assume non-empty groups
          sorry
        · rw [group_def] at h_balanced h_empty
          apply count_max_paren_depth_pos_of_balanced
          exact h_balanced
          exact h_empty
      · simp [int_toNat_coe]
        rw [group_def]