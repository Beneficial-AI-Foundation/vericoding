-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_char (c : Char) (s : String) : Nat := sorry

def reverse_in_parentheses (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_preserved (s : String) : 
  (reverse_in_parentheses s).length = s.length := by
  sorry

theorem preserves_parens_count (s : String) : 
  (count_char '(' s = count_char '(' (reverse_in_parentheses s)) ∧ 
  (count_char ')' s = count_char ')' (reverse_in_parentheses s)) := by
  sorry

theorem no_parens_unchanged (s : String) 
  (h : ∀ c ∈ s.data, c ≠ '(' ∧ c ≠ ')') :
  reverse_in_parentheses s = s := by
  sorry

/-
info: 'h(le)lo'
-/
-- #guard_msgs in
-- #eval reverse_in_parentheses "h(el)lo"

/-
info: 'a (b c (d e))'
-/
-- #guard_msgs in
-- #eval reverse_in_parentheses "a ((d e) c b)"

/-
info: 'one (ruof (three) owt)'
-/
-- #guard_msgs in
-- #eval reverse_in_parentheses "one (two (three) four)"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded