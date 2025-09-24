-- <vc-preamble>
partial def Sum_ (xs : Array Int) : Int :=
if xs.size = 0 then
0
else
Sum_ (xs.extract 0 (xs.size - 1)) + xs[xs.size - 1]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SumArray (xs : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SumArray_spec (xs : Array Int) (s : Int) :
s = SumArray xs → s = Sum_ xs :=
sorry
-- </vc-theorems>