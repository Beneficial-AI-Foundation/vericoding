-- <vc-preamble>
/- Helper function to check if sub is a subrange of main starting at position i -/
def isSubrangeAt (main : List Int) (sub : List Int) (i : Int) : Bool :=
  if i < 0 ∨ i + sub.length > main.length then false
  else sub = (main.drop i.natAbs).take sub.length

@[reducible, simp]
def isSubArray_precond (main : Array Int) (sub : Array Int) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()