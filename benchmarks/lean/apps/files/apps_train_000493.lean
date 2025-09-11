-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_parentheses (s : String) : String := sorry

theorem reverse_parentheses_length 
  (s : String) : 
  s.length = (reverse_parentheses s).length + s.data.count '(' + s.data.count ')' := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_parentheses_no_parens
  (s : String) :
  ¬ ((reverse_parentheses s).contains '(') ∧ ¬ ((reverse_parentheses s).contains ')') :=
  sorry

theorem reverse_parentheses_empty_parens :
  reverse_parentheses "()" = "" :=
  sorry

theorem reverse_parentheses_identity_no_parens
  (s : String) 
  (h : ¬ s.contains '(' ∧ ¬ s.contains ')') :
  reverse_parentheses s = s :=
  sorry

theorem reverse_parentheses_empty_string :
  reverse_parentheses "" = "" :=
  sorry

/-
info: 'dcba'
-/
-- #guard_msgs in
-- #eval reverse_parentheses "(abcd)"

/-
info: 'iloveu'
-/
-- #guard_msgs in
-- #eval reverse_parentheses "(u(love)i)"

/-
info: 'apmnolkjihgfedcbq'
-/
-- #guard_msgs in
-- #eval reverse_parentheses "a(bcdefghijkl(mno)p)q"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded