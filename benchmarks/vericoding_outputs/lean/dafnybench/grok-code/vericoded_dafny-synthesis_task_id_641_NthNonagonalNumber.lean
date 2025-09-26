import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def NthNonagonalNumber (n : Int) : Int :=
n * (7 * n - 5) / 2
-- </vc-definitions>

-- <vc-theorems>
theorem NthNonagonalNumber_spec (n : Int) :
n ≥ 0 → NthNonagonalNumber n = n * (7 * n - 5) / 2 :=
fun _ => by rw [NthNonagonalNumber]
-- </vc-theorems>
