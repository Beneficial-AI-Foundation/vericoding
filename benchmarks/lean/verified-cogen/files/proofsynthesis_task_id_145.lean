-- <vc-preamble>
-- Define Int bounds for the precondition
axiom Int.neg_div_two : Int
axiom Int.pos_div_two : Int
axiom Int.bounds_assumption : Int.neg_div_two < Int.pos_div_two

@[reducible, simp]
def maxDifference_precond (arr : Array Int) : Prop :=
  arr.size > 0 ∧ (∀ i, i < arr.size → Int.neg_div_two < arr[i]! ∧ arr[i]! < Int.pos_div_two)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()