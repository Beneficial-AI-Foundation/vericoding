import Mathlib
-- <vc-preamble>
@[reducible, simp]
def inner_expr_replace_blanks_with_chars (str1 : Array Char) (ch : Char) (i : Nat) : Char :=
  if str1[i]! = Char.ofNat 32 then ch else str1[i]!

@[reducible, simp]
def replaceBlanksWithChars_precond (str1 : Array Char) (ch : Char) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def replaceBlanksWithChars (str1 : Array Char) (ch : Char) (h_precond : replaceBlanksWithChars_precond str1 ch) : Array Char :=
  Array.ofFn (fun j : Fin str1.size => inner_expr_replace_blanks_with_chars str1 ch j.1)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def replaceBlanksWithChars_postcond (str1 : Array Char) (ch : Char) (result : Array Char) (h_precond : replaceBlanksWithChars_precond str1 ch) : Prop :=
  str1.size = result.size ∧
  (∀ i, i < str1.size → result[i]! = inner_expr_replace_blanks_with_chars str1 ch i)

theorem replaceBlanksWithChars_spec_satisfied (str1 : Array Char) (ch : Char) (h_precond : replaceBlanksWithChars_precond str1 ch) :
    replaceBlanksWithChars_postcond str1 ch (replaceBlanksWithChars str1 ch h_precond) h_precond := by
  constructor
  · simp [replaceBlanksWithChars]
  · intro i hi
    simpa [replaceBlanksWithChars, Array.get!, hi]
-- </vc-theorems>
