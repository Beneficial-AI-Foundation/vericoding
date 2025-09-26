import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this implementation
-- </vc-helpers>

-- <vc-definitions>
def power {n : Nat} (a : Vector Int n) (b : Vector Nat n) : Vector Int n :=
Vector.ofFn (fun i => a[i] ^ b[i])
-- </vc-definitions>

-- <vc-theorems>
theorem power_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n) :
  (power a b).toList.length = n ∧
  ∀ i : Fin n, (power a b)[i] = (a[i]) ^ (b[i]) :=
⟨by simp [power, Vector.toList_ofFn], fun i => by simp [power]⟩
-- </vc-theorems>
