-- <vc-preamble>
@[reducible, simp]
def inner_expr_replace_blanks_with_chars (str1 : Array Char) (ch : Char) (i : Nat) : Char :=
  if str1[i]! = Char.ofNat 32 then ch else str1[i]!

@[reducible, simp]
def replaceBlanksWithChars_precond (str1 : Array Char) (ch : Char) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()