-- <vc-preamble>
@[reducible, simp]
def replaceChars_precond (str1 : Array Char) (old_char : Char) (new_char : Char) := True
-- </vc-preamble>

-- <vc-helpers>
/- Helper function for character replacement -/
def inner_expr_replace_chars (str1 : Array Char) (old_char : Char) (new_char : Char) (i : Nat) : Char :=
  if str1[i]! = old_char then new_char else str1[i]!
-- </vc-helpers>

def main : IO Unit := return ()