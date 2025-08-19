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

-- LLM HELPER
def is_subsequence (sub : List Char) (main : List Char) : Bool :=
  match sub with
  | [] => true
  | h :: t => 
    match main with
    | [] => false
    | mh :: mt => if h = mh then is_subsequence t mt else is_subsequence sub mt

-- LLM HELPER
def balanced_paren_non_computable (s : String) (open_char : Char) (close_char : Char) : Bool :=
  let chars := s.toList
  let rec check_balance (lst : List Char) (depth : Int) : Bool :=
    match lst with
    | [] => depth = 0
    | h :: t => 
      if h = open_char then
        check_balance t (depth + 1)
      else if h = close_char then
        if depth > 0 then check_balance t (depth - 1) else false
      else
        check_balance t depth
  check_balance chars 0

-- LLM HELPER
def count_max_paren_depth (s : String) : Nat :=
  let chars := s.toList
  let rec max_depth (lst : List Char) (current_depth : Nat) (max_so_far : Nat) : Nat :=
    match lst with
    | [] => max_so_far
    | h :: t => 
      if h = '(' then
        let new_depth := current_depth + 1
        max_depth t new_depth (max new_depth max_so_far)
      else if h = ')' then
        let new_depth := if current_depth > 0 then current_depth - 1 else 0
        max_depth t new_depth max_so_far
      else
        max_depth t current_depth max_so_far
  max_depth chars 0 0

-- LLM HELPER
def find_valid_subsequence (s : String) : Option String :=
  let chars := s.toList
  let parens := chars.filter (fun c => c = '(' ∨ c = ')')
  let rec try_subsequences (remaining : List Char) (current : List Char) : Option (List Char) :=
    if current.length ≥ 4 then
      let candidate := String.mk current
      if balanced_paren_non_computable candidate '(' ')' ∧ 2 ≤ count_max_paren_depth candidate then
        some current
      else
        match remaining with
        | [] => none
        | h :: t => try_subsequences t (current ++ [h])
    else
      match remaining with
      | [] => none
      | h :: t => try_subsequences t (current ++ [h])
  match try_subsequences parens [] with
  | some result => some (String.mk result)
  | none => none

def implementation (lst: String) : Bool := 
  if lst.toList.all (fun x => x = '(' ∨ x = ')') then
    match find_valid_subsequence lst with
    | some _ => true
    | none => false
  else
    false

-- LLM HELPER
lemma exists_valid_subsequence_iff (s : String) :
  (∃ x : String, is_subsequence x.toList s.toList ∧ balanced_paren_non_computable x '(' ')' ∧ 2 ≤ count_max_paren_depth x) ↔
  find_valid_subsequence s ≠ none := by
  sorry

theorem correctness
(string: String)
: problem_spec implementation string := by
  unfold problem_spec
  simp only [implementation]
  use (if string.toList.all (fun x => x = '(' ∨ x = ')') then
         match find_valid_subsequence string with
         | some _ => true
         | none => false
       else false)
  constructor
  · rfl
  · intro h
    simp only [ite_eq_iff]
    cases' h' : string.toList.all (fun x => x = '(' ∨ x = ')') with
    · simp [h']
      constructor
      · intro
        exfalso
        exact h h'
      · intro h_ex
        cases h_ex
    · simp [h', h]
      rw [exists_valid_subsequence_iff]
      cases h_sub : find_valid_subsequence string with
      | none => simp
      | some val => simp