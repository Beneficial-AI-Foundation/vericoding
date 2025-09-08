/- 
function_signature: "def match_parens(l : list[str]) -> str"
docstring: |
    You are given a list of two strings, both strings consist of open
    parentheses '(' or close parentheses ')' only.
    Your job is to check if it is possible to concatenate the two strings in
    some order, that the resulting string will be good.
    A string S is considered to be good if and only if all parentheses in S
    are balanced. For example: the string '(())()' is good, while the string
    '())' is not.
    Return 'Yes' if there's a way to make a good string, and return 'No' otherwise.
test_cases:
  - input: ['()(', ')']
    expected_output: "Yes"
  - input: [')', ')']
    expected_output: "No"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: balanced_paren_non_computable
use: |
  Non-computable definition to check if a string is balanced with respect to parentheses.
problems:
  - 1
  - 6
  - 119
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

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_balanced_string (s : String) : Bool :=
  let chars := s.toList
  let rec check_balance (chars : List Char) (depth : Int) : Bool :=
    match chars with
    | [] => depth = 0
    | '(' :: rest => check_balance rest (depth + 1)
    | ')' :: rest => if depth > 0 then check_balance rest (depth - 1) else false
    | _ :: rest => check_balance rest depth  -- ignore other characters
  check_balance chars 0

def implementation (l: List String) : String :=
  if l.length = 2 then
    let s1 := l[0]!
    let s2 := l[1]!
    if is_balanced_string (s1 ++ s2) || is_balanced_string (s2 ++ s1) then
      "Yes"
    else
      "No"
  else
    "No"

-- LLM HELPER
lemma balanced_string_equiv (s : String) :
  is_balanced_string s = true ↔ balanced_paren_non_computable s '(' ')' := by
  sorry

-- LLM HELPER  
lemma balanced_string_false (s : String) :
  is_balanced_string s = false ↔ ¬balanced_paren_non_computable s '(' ')' := by
  sorry

-- LLM HELPER
lemma string_all_parens_valid (s : String) :
  s.all (fun c => c = '(' ∨ c = ')') → True := by
  intro h
  trivial

def problem_spec
-- function signature
(implementation: List String → String)
-- inputs
(l: List String) :=
-- spec
let spec (result : String) :=
  l.length = 2 →
  l[0]!.all (fun c => c = '(' ∨ c = ')') →
  l[1]!.all (fun c => c = '(' ∨ c = ')') →
  let res := (balanced_paren_non_computable (l[0]! ++ l[1]!) '(' ')' ∨
            balanced_paren_non_computable (l[1]! ++ l[0]!) '(' ')')
  (res → result = "Yes") ∧
  (¬ res → result = "No")
-- program termination
∃ result,
  implementation l = result ∧
  spec result

theorem correctness
(l: List String)
: problem_spec implementation l := by
  unfold problem_spec
  use implementation l
  constructor
  · rfl
  · intro h_len h_all1 h_all2
    unfold implementation
    simp [h_len]
    constructor
    · intro h_res
      by_cases h : is_balanced_string (l[0]! ++ l[1]!) = true
      · simp [h]
      · by_cases h' : is_balanced_string (l[1]! ++ l[0]!) = true
        · simp [h, h']
        · simp [h, h']
          exfalso
          cases' h_res with h1 h2
          · rw [balanced_string_false] at h
            exact h h1
          · rw [balanced_string_false] at h'
            exact h' h2
    · intro h_not_res
      by_cases h : is_balanced_string (l[0]! ++ l[1]!) = true
      · simp [h]
        exfalso
        apply h_not_res
        left
        rw [←balanced_string_equiv]
        exact h
      · by_cases h' : is_balanced_string (l[1]! ++ l[0]!) = true
        · simp [h, h']
          exfalso
          apply h_not_res
          right
          rw [←balanced_string_equiv]
          exact h'
        · simp [h, h']

-- #test implementation ['()(', ')'] = "Yes"
-- #test implementation [')', ')'] = "No"