import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed for this file.
-- </vc-helpers>

-- <vc-definitions>
def SumOfFourthPowerOfOddNumbers (n : Int) : Int :=
n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15
-- </vc-definitions>

-- <vc-theorems>
theorem SumOfFourthPowerOfOddNumbers_spec (n : Int) :
n > 0 →
SumOfFourthPowerOfOddNumbers n =
n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15 :=
by
  intro _
  rfl
-- </vc-theorems>
