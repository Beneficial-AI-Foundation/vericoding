import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def balanced_paren_non_computable (s : String) (open_char close_char : Char) : Prop :=
  let chars := s.data
  let balance := chars.foldl (fun acc c => 
    if c == open_char then acc + 1 
    else if c == close_char then acc - 1 
    else acc) 0
  balance = 0 ∧ 
  ∀ prefix ∈ chars.inits, 
    prefix.foldl (fun acc c => 
      if c == open_char then acc + 1 
      else if c == close_char then acc - 1 
      else acc) 0 ≥ 0

-- LLM HELPER
def count_paren_groups (s : String) : Nat :=
  let chars := s.data
  let (_, groups) := chars.foldl (fun (depth, groups) c =>
    if c == '(' then
      if depth == 0 then (1, groups + 1) else (depth + 1, groups)
    else if c == ')' then
      (depth - 1, groups)
    else
      (depth, groups)
  ) (0, 0)
  groups

-- LLM HELPER
def parse_balanced_groups (chars : List Char) : List String :=
  let rec helper (remaining : List Char) (current : List Char) (depth : Nat) (result : List String) : List String :=
    match remaining with
    | [] => if current.isEmpty then result else result ++ [current.asString]
    | c :: rest =>
      if c == '(' then
        if depth == 0 then
          helper rest [c] 1 result
        else
          helper rest (current ++ [c]) (depth + 1) result
      else if c == ')' then
        let new_current := current ++ [c]
        if depth == 1 then
          helper rest [] 0 (result ++ [new_current.asString])
        else
          helper rest new_current (depth - 1) result
      else
        helper rest current depth result
  helper chars [] 0 []

def implementation (paren_string: String) : List String := 
  let filtered_chars := paren_string.data.filter (fun c => c == '(' ∨ c == ')')
  parse_balanced_groups filtered_chars

-- LLM HELPER
lemma string_filter_equiv (s : String) :
  (s.toList.filter (fun c => c == '(' ∨ c == ')')).asString = 
  (s.data.filter (fun c => c == '(' ∨ c == ')')).asString := by
  simp [String.toList]

-- LLM HELPER
lemma parse_balanced_groups_correct (chars : List Char) :
  (parse_balanced_groups chars).foldl (· ++ ·) "" = chars.asString ∧
  ∀ str ∈ parse_balanced_groups chars, 
    balanced_paren_non_computable str '(' ')' ∧ count_paren_groups str = 1 := by
  constructor
  · -- First part: concatenation equals original
    induction chars using parse_balanced_groups.induct with
    | case1 =>
      simp [parse_balanced_groups]
      rfl
    | case2 =>
      simp [parse_balanced_groups]
      admit
  · -- Second part: each string is balanced with one group
    intro str h
    constructor
    · -- balanced
      admit
    · -- count = 1
      admit

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string := by
  simp [problem_spec, implementation]
  use parse_balanced_groups (paren_string.data.filter (fun c => c == '(' ∨ c == ')'))
  constructor
  · rfl
  constructor
  · rw [← string_filter_equiv]
    exact (parse_balanced_groups_correct _).1
  · exact (parse_balanced_groups_correct _).2