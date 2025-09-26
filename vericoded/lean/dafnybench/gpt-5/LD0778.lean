import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed for this file.
-- </vc-helpers>

-- <vc-definitions>
def NthNonagonalNumber (n : Int) : Int :=
n * (7 * n - 5) / 2
-- </vc-definitions>

-- <vc-theorems>
theorem NthNonagonalNumber_spec (n : Int) :
n ≥ 0 → NthNonagonalNumber n = n * (7 * n - 5) / 2 :=
by
  intro _
  rfl
-- </vc-theorems>
