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

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string
:= by
  let result := implementation paren_string
  use result
  constructor
  · rfl
  · constructor
    · simp [implementation, List.length_map]
    · intro i h_i group_def h_balanced
      simp [implementation] at group_def ⊢
      have h_bound : i < (paren_string.split (fun x => x = ' ')).length := by
        rw [implementation] at h_i
        simp [List.length_map] at h_i
        exact h_i
      constructor
      · simp [Nat.cast_pos]
        by_cases h_empty : (paren_string.split (fun x => x = ' '))[i]! = ""
        · simp [h_empty, count_max_paren_depth, count_max_paren_depth_helper]
        · have h_contains_paren : '(' ∈ (paren_string.split (fun x => x = ' '))[i]!.toList ∨ ')' ∈ (paren_string.split (fun x => x = ' '))[i]!.toList := by
            cases' h_balanced with h_prefix h_equal
            rw [balanced_paren_non_computable] at h_balanced
            simp at h_balanced
            cases' h_balanced with h_prefix h_equal
            by_contra h_no_parens
            push_neg at h_no_parens
            have h_count_left : (paren_string.split (fun x => x = ' '))[i]!.toList.count '(' = 0 := by
              rw [List.count_eq_zero]
              exact h_no_parens.1
            have h_count_right : (paren_string.split (fun x => x = ' '))[i]!.toList.count ')' = 0 := by
              rw [List.count_eq_zero]  
              exact h_no_parens.2
            rw [h_count_left, h_count_right] at h_equal
            simp at h_equal
            have h_no_parens_at_all : ∀ c ∈ (paren_string.split (fun x => x = ' '))[i]!.toList, c ≠ '(' ∧ c ≠ ')' := by
              intro c hc
              exact ⟨h_no_parens.1 c hc, h_no_parens.2 c hc⟩
            cases h_contains_paren with
            | inl h_left => 
              have := h_no_parens.1 '(' h_left
              contradiction
            | inr h_right =>
              have := h_no_parens.2 ')' h_right  
              contradiction
          apply Nat.pos_of_ne_zero
          intro h_zero
          unfold count_max_paren_depth at h_zero
          cases h_contains_paren with
          | inl h_left =>
            have h_depth_pos : count_max_paren_depth_helper (paren_string.split (fun x => x = ' '))[i]! 0 0 > 0 := by
              unfold count_max_paren_depth_helper
              have h_nonempty : ¬(paren_string.split (fun x => x = ' '))[i]!.isEmpty := by
                rw [String.isEmpty_iff]
                exact h_empty
              simp [h_nonempty]
              split_ifs with h_first_char
              · simp [Nat.max_def]
                norm_cast
                simp
              · split_ifs
                · apply Nat.pos_of_ne_zero
                  intro h_contra
                  rw [h_contra] at h_zero
                  exact Nat.not_lt_zero 0 (Nat.pos_of_ne_zero h_contra)
                · apply Nat.pos_of_ne_zero  
                  intro h_contra
                  rw [h_contra] at h_zero
                  exact Nat.not_lt_zero 0 (Nat.pos_of_ne_zero h_contra)
            rw [h_zero] at h_depth_pos
            exact Nat.not_lt_zero 0 h_depth_pos
          | inr h_right =>
            have h_depth_pos : count_max_paren_depth_helper (paren_string.split (fun x => x = ' '))[i]! 0 0 > 0 := by
              unfold count_max_paren_depth_helper  
              have h_nonempty : ¬(paren_string.split (fun x => x = ' '))[i]!.isEmpty := by
                rw [String.isEmpty_iff]
                exact h_empty
              simp [h_nonempty]
              split_ifs with h_first_char
              · simp [Nat.max_def]
                norm_cast
                simp  
              · split_ifs
                · apply Nat.pos_of_ne_zero
                  intro h_contra
                  rw [h_contra] at h_zero  
                  exact Nat.not_lt_zero 0 (Nat.pos_of_ne_zero h_contra)
                · apply Nat.pos_of_ne_zero
                  intro h_contra
                  rw [h_contra] at h_zero
                  exact Nat.not_lt_zero 0 (Nat.pos_of_ne_zero h_contra)
            rw [h_zero] at h_depth_pos
            exact Nat.not_lt_zero 0 h_depth_pos
      · simp [Int.toNat_of_nonneg (Nat.cast_nonneg _)]