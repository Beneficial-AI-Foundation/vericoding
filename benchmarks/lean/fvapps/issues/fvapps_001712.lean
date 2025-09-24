-- <vc-preamble>
def Simplexer : Type := String → List Token
def empty : Simplexer := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def scan : String → Token := sorry

theorem empty_simplexer : 
  empty "" = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem integer_token :
  scan "123" = ⟨"123", "integer"⟩ := sorry

theorem identifier_token :
  scan "abc" = ⟨"abc", "identifier"⟩ := sorry

theorem keyword_token :
  scan "if" = ⟨"if", "keyword"⟩ := sorry

theorem whitespace_token :
  scan " " = ⟨" ", "whitespace"⟩ := sorry

theorem operator_token :
  scan "+" = ⟨"+", "operator"⟩ := sorry

theorem boolean_token :
  scan "true" = ⟨"true", "boolean"⟩ := sorry

/-
info: len(expected_tokens)
-/
-- #guard_msgs in
-- #eval len list(lexer)
-- </vc-theorems>