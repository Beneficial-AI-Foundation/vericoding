import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Vector zipWith operation for element-wise operations
-- This helper enables element-wise modulus operation on vectors
-- </vc-helpers>

-- <vc-definitions>
def remainder {n : Nat} (a b : Vector Int n) : Vector Int n :=
Vector.zipWith (· % ·) a b
-- </vc-definitions>

-- <vc-theorems>
theorem remainder_spec {n : Nat} (a b : Vector Int n)
  (h : ∀ i : Fin n, b[i] ≠ 0) :
  let ret := remainder a b
  (ret.toList.length = n) ∧
  (∀ i : Fin n, ret[i] = a[i] % b[i]) :=
⟨by simp [remainder, Vector.toList_zipWith], by intro i; simp [remainder]⟩
-- </vc-theorems>
