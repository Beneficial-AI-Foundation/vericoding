import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def zipWith' {α β γ : Type*} {n : Nat} (f : α → β → γ) (v₁ : Vector α n) (v₂ : Vector β n) : Vector γ n :=
  ⟨Array.ofFn fun i => f v₁[i] v₂[i], by simp [Array.size_ofFn]⟩
-- </vc-helpers>

-- <vc-definitions>
def power {n : Nat} (a : Vector Int n) (b : Vector Nat n) : Vector Int n :=
zipWith' (fun a b => a ^ b) a b
-- </vc-definitions>

-- <vc-theorems>
theorem power_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n) :
  (power a b).toList.length = n ∧
  ∀ i : Fin n, (power a b)[i] = (a[i]) ^ (b[i]) :=
by
  constructor
  · -- Length property
    simp [power, zipWith', Vector.toList_mk, Array.toList_ofFn]
  · -- Element-wise property  
    intro i
    simp [power, zipWith', Vector.getElem_mk, Array.getElem_ofFn]
-- </vc-theorems>
