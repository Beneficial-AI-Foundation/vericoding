import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Define sum of first n natural numbers
def sumFirstN (n : Int) : Int := (n * (n + 1)) / 2

-- LLM HELPER: Define sum of cubes of first n natural numbers
def sumCubesFirstN (n : Int) : Int := (n * n * (n + 1) * (n + 1)) / 4
-- </vc-helpers>

-- <vc-definitions>
def DifferenceSumCubesAndSumNumbers (n : Int) : Int :=
if n ≥ 0 then sumCubesFirstN n - sumFirstN n else 0
-- </vc-definitions>

-- <vc-theorems>
theorem DifferenceSumCubesAndSumNumbers_spec (n : Int) :
n ≥ 0 →
DifferenceSumCubesAndSumNumbers n = (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2 :=
by
  intro h_nonneg
  unfold DifferenceSumCubesAndSumNumbers sumCubesFirstN sumFirstN
  simp [if_pos h_nonneg]
-- </vc-theorems>
