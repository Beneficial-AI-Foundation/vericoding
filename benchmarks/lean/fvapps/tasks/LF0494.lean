-- <vc-preamble>
inductive CharIn (s : String) where
  | mk (c : Char) (h : s.data.contains c) : CharIn s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validParens (s : String) : Bool :=
sorry

def isSubsequence (s1 s2 : String) : Bool :=
sorry

def minRemoveToMakeValid (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_contains_valid_chars (s : String) :
  ∀ c, (minRemoveToMakeValid s).data.contains c →
    c = '(' ∨ c = ')' ∨ c = 'a' ∨ c = 'b' ∨ c = 'c' :=
sorry

theorem result_has_balanced_parens (s : String) :
  validParens (minRemoveToMakeValid s) :=
sorry

theorem result_is_subsequence (s : String) :
  isSubsequence (minRemoveToMakeValid s) s :=
sorry

theorem no_parens_unchanged (s : String) :
  (∀ c, s.data.contains c → c ≠ '(' ∧ c ≠ ')') →
  minRemoveToMakeValid s = s :=
sorry

theorem empty_string :
  minRemoveToMakeValid "" = "" :=
sorry

theorem only_open_brackets (n : Nat) :
  minRemoveToMakeValid (String.mk (List.replicate n '(')) = "" :=
sorry

theorem only_close_brackets (n : Nat) :
  minRemoveToMakeValid (String.mk (List.replicate n ')')) = "" :=
sorry
-- </vc-theorems>