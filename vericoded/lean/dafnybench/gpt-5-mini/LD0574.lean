import Mathlib
-- <vc-preamble>
partial def Sum_ (xs : Array Int) : Int :=
if xs.size = 0 then
0
else
Sum_ (xs.extract 0 (xs.size - 1)) + xs[xs.size - 1]!
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Helper definitions for SumArray and Sum_ (none required at the moment)

-- </vc-helpers>

-- <vc-definitions>
def SumArray (xs : Array Int) : Int :=
Sum_ xs
-- </vc-definitions>

-- <vc-theorems>
theorem SumArray_spec (xs : Array Int) (s : Int) :
s = SumArray xs → s = Sum_ xs :=
by
  intro h
  unfold SumArray at h
  exact h
-- </vc-theorems>
