import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed for this file.
-- </vc-helpers>

-- <vc-definitions>
def DifferenceSumCubesAndSumNumbers (n : Int) : Int :=
(n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
-- </vc-definitions>

-- <vc-theorems>
theorem DifferenceSumCubesAndSumNumbers_spec (n : Int) :
n ≥ 0 →
DifferenceSumCubesAndSumNumbers n = (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2 :=
by
  intro h
  rfl
-- </vc-theorems>
