-- <vc-preamble>
def validParens (s : String) : Bool := sorry

def isSubsequence (s1 s2 : String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minRemoveToMakeValid (s : String) : String := sorry

inductive CharIn (s : String) where
  | mk (c : Char) (h : s.data.contains c) : CharIn s

-- All chars in result are valid
-- </vc-definitions>

-- <vc-theorems>
theorem result_contains_valid_chars (s : String) :
  ∀ c, (minRemoveToMakeValid s).data.contains c →
    c = '(' ∨ c = ')' ∨ c = 'a' ∨ c = 'b' ∨ c = 'c' := sorry

-- Result has balanced parentheses

theorem result_has_balanced_parens (s : String) :
  validParens (minRemoveToMakeValid s) := sorry

-- Result is a subsequence of input

theorem result_is_subsequence (s : String) :
  isSubsequence (minRemoveToMakeValid s) s := sorry

-- Strings without parens are unchanged 

theorem no_parens_unchanged (s : String) :
  (∀ c, s.data.contains c → c ≠ '(' ∧ c ≠ ')') →
  minRemoveToMakeValid s = s := sorry

-- Empty string case

theorem empty_string :
  minRemoveToMakeValid "" = "" := sorry

-- Only open brackets become empty

theorem only_open_brackets (n : Nat) :
  minRemoveToMakeValid (String.mk (List.replicate n '(')) = "" := sorry 

-- Only close brackets become empty  

theorem only_close_brackets (n : Nat) :
  minRemoveToMakeValid (String.mk (List.replicate n ')')) = "" := sorry

/-
info: 'lee(t(c)o)de'
-/
-- #guard_msgs in
-- #eval minRemoveToMakeValid "lee(t(c)o)de)"

/-
info: 'ab(c)d'
-/
-- #guard_msgs in
-- #eval minRemoveToMakeValid "a)b(c)d"

/-
info: ''
-/
-- #guard_msgs in
-- #eval minRemoveToMakeValid "))(("
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded