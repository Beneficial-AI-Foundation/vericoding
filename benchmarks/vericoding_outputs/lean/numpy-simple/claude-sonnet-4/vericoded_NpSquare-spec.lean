import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def square {n : Nat} (arr : Vector Int n) : Vector Int n :=
Vector.map (fun x => x * x) arr
-- </vc-definitions>

-- <vc-theorems>
theorem square_spec {n : Nat} (arr : Vector Int n) :
  (square arr).toList.length = n ∧
  ∀ i : Fin n, (square arr)[i] = (arr[i]) * (arr[i]) :=
⟨by simp [square], by intro i; simp [square, Vector.get_map]⟩
-- </vc-theorems>
