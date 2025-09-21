-- <vc-preamble>
def sqrt (x : Int) (r : Int) : Bool :=
r*r ≤ x ∧ (r+1)*(r+1) > x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mySqrt (x : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mySqrt_spec (x : Int) :
x ≥ 0 → sqrt x (mySqrt x) :=
sorry
-- </vc-theorems>