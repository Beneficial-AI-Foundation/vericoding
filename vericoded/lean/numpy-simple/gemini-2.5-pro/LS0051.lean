import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

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
  constructor
  · simp [square, Vector.toList_map, List.length_map, Vector.length_toList]
  · intro i
    simp [square, Vector.get_map]
-- </vc-theorems>
