-- <vc-preamble>
@[reducible, simp]
def replaceChars_precond (str1 : Array Char) (old_char : Char) (new_char : Char) := True
-- </vc-preamble>

-- <vc-helpers>
/- Helper function for character replacement -/
def inner_expr_replace_chars (str1 : Array Char) (old_char : Char) (new_char : Char) (i : Nat) : Char :=
  if str1[i]! = old_char then new_char else str1[i]!
-- </vc-helpers>

-- <vc-definitions>
def replaceChars (str1 : Array Char) (old_char : Char) (new_char : Char) (h_precond : replaceChars_precond str1 old_char new_char) : Array Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def replaceChars_postcond (str1 : Array Char) (old_char : Char) (new_char : Char) (result : Array Char) (h_precond : replaceChars_precond str1 old_char new_char) :=
  str1.size = result.size ∧ 
  (∀ i, i < str1.size → result[i]! = inner_expr_replace_chars str1 old_char new_char i)

theorem replaceChars_spec_satisfied (str1 : Array Char) (old_char : Char) (new_char : Char) (h_precond : replaceChars_precond str1 old_char new_char) :
    replaceChars_postcond str1 old_char new_char (replaceChars str1 old_char new_char h_precond) h_precond := by
  sorry
-- </vc-theorems>