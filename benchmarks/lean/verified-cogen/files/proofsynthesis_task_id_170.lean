-- <vc-preamble>
/- Recursive function to compute sum of list elements -/
def sumTo (arr : List Int) : Int :=
  match arr with
  | [] => 0
  | _ :: xs => sumTo xs + arr.getLast!
  termination_by arr.length

@[reducible, simp]
def sumRangeList_precond (arr : Array Int) (start : Nat) (endVal : Nat) : Prop :=
  start ≤ endVal ∧ endVal < arr.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()