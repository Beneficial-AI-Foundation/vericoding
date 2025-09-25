-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MultipleReturns (x y : Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem MultipleReturns_spec (x y : Int) :
let (more, less) := MultipleReturns x y
more = x + y ∧ less = x - y :=
sorry
-- </vc-theorems>