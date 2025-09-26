import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: No additional helpers needed for this implementation
-- </vc-helpers>

-- <vc-definitions>
def NthNonagonalNumber (n : Int) : Int :=
n * (7 * n - 5) / 2
-- </vc-definitions>

-- <vc-theorems>
theorem NthNonagonalNumber_spec (n : Int) :
n ≥ 0 → NthNonagonalNumber n = n * (7 * n - 5) / 2 :=
fun h => rfl
-- </vc-theorems>
