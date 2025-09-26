import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Small helper lemmas (placeholders) that can be used in proofs if needed.
theorem Int_sum_formula_trivial (n : Int) : n ≥ 0 → (n * (n + 1)) / 2 = (n * (n + 1)) / 2 := fun _ => rfl

theorem Int_sum_cubes_formula_trivial (n : Int) : n ≥ 0 → (n * n * (n + 1) * (n + 1)) / 4 = (n * n * (n + 1) * (n + 1)) / 4 := fun _ => rfl
-- </vc-helpers>

-- <vc-definitions>
def DifferenceSumCubesAndSumNumbers (n : Int) : Int :=
(n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
-- </vc-definitions>

-- <vc-theorems>
theorem DifferenceSumCubesAndSumNumbers_spec (n : Int) :
n ≥ 0 →
DifferenceSumCubesAndSumNumbers n = (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2 :=
by intro _; rfl
-- </vc-theorems>
