-- <vc-preamble>
-- Function to compute sum of negative numbers from sequence recursively
def sum_negative_to (seq : List Int) : Int :=
  match seq with
  | [] => 0
  | h :: t => sum_negative_to t + if h < 0 then h else 0

@[reducible, simp]
def sumNegatives_precond (arr : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()