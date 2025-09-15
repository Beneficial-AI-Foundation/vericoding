-- <vc-preamble>
/- Helper function to check if a character is a digit -/
def isDigit (c : Char) : Bool :=
  (c.val >= 48) ∧ (c.val <= 57)

/- Recursive function to count digits in a sequence of characters -/
def countDigitsRecursively (seq : List Char) : Nat :=
  match seq with
  | [] => 0
  | h :: t => countDigitsRecursively t + if isDigit h then 1 else 0
termination_by seq.length

@[reducible, simp]
def countDigits_precond (text : Array Char) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()