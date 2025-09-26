import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def ComputeIsEven (x : Int) : Bool :=
x % 2 == 0
-- </vc-definitions>

-- <vc-theorems>
theorem ComputeIsEven_spec (x : Int) :
ComputeIsEven x = (x % 2 = 0) :=
by
  unfold ComputeIsEven
  simp only [BEq.beq, decide_eq_true_iff]
-- </vc-theorems>
