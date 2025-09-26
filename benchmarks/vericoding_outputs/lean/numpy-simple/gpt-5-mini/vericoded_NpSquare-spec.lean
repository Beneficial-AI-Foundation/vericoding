import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helper lemmas required; rely on Vector.map and stdlib simp lemmas

-- </vc-helpers>

-- <vc-definitions>
def square {n : Nat} (arr : Vector Int n) : Vector Int n :=
arr.map fun x => x * x
-- </vc-definitions>

-- <vc-theorems>
theorem square_spec {n : Nat} (arr : Vector Int n) :
  (square arr).toList.length = n ∧
  ∀ i : Fin n, (square arr)[i] = (arr[i]) * (arr[i]) :=
by
  dsimp [square]
  constructor
  · simp
  · intro i; simp

-- </vc-theorems>
