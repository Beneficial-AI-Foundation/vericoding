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

-- LLM HELPER
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

-- LLM HELPER
def balanced_paren_non_computable
(paren_string: String) (bracket_type_left : Char) (bracket_type_right: Char): Prop
:=
let chars := paren_string.toList;
(∀ (i : ℕ), i ≤ chars.length → ((chars.take i).count bracket_type_right) ≤ ((chars.take i).count bracket_type_left)) ∧
(chars.count bracket_type_left = chars.count bracket_type_right)

-- LLM HELPER
def count_max_paren_depth_helper
(paren_string: String) (num_open: Int) (max_depth: Nat): Nat :=
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
    simp only [String.length_drop]
    have h_pos : 0 < paren_string.length := by
      by_contra h
      simp at h
      have : paren_string.isEmpty := String.length_eq_zero.mp (Nat.le_zero_eq.mp h)
      contradiction
    exact Nat.sub_lt h_pos (by norm_num)
  }

-- LLM HELPER
def count_max_paren_depth
(paren_string: String): Nat :=
count_max_paren_depth_helper paren_string 0 0

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

def problem_spec
(implementation: String → List Int)
(paren_string: String)
:=
∃ result, implementation paren_string = result ∧
let paren_space_split := paren_string.split (fun x => x = ' ') in
result.length = paren_space_split.length ∧
∀ i, i < result.length →
  let group := paren_space_split.get? i |>.getD ""
  balanced_paren_non_computable group '(' ')' →
    0 ≤ (result.get? i |>.getD 0) ∧ 
    count_max_paren_depth group = ((result.get? i |>.getD 0).toNat)

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string
:= by
  simp [problem_spec, implementation]
  let groups := paren_string.split (fun x => x = ' ')
  use groups.map (fun group => (count_max_paren_depth group : Int))
  constructor
  · rfl
  constructor
  · exact map_preserves_length groups _
  · intros i h_i h_balanced
    have h_bound : i < groups.length := by rwa [←map_preserves_length] at h_i
    constructor
    · have h_ge : 0 ≤ (count_max_paren_depth (groups[i]'h_bound) : Int) := Int.coe_nat_nonneg _
      rw [List.get?_eq_getElem, getElem_map]
      exact h_ge
    · rw [List.get?_eq_getElem, getElem_map]
      rw [Int.toNat_of_nonneg (Int.coe_nat_nonneg _)]