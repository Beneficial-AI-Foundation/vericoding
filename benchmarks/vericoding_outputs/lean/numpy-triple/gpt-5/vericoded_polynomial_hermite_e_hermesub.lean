import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def hermesubFn {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) :
    Fin (max n m) → Float :=
  fun i =>
    (if h₁ : i.val < n then c1.get ⟨i.val, h₁⟩ else (0 : Float)) -
    (if h₂ : i.val < m then c2.get ⟨i.val, h₂⟩ else (0 : Float))
-- </vc-helpers>

-- <vc-definitions>
def hermesub {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : Id (Vector Float (max n m)) :=
  pure <| Vector.ofFn (hermesubFn c1 c2)
-- </vc-definitions>

-- <vc-theorems>
theorem hermesub_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) :
    ⦃⌜True⌝⦄
    hermesub c1 c2
    ⦃⇓result => ⌜∀ i : Fin (max n m), 
      result.get i = (if h₁ : i.val < n then c1.get ⟨i.val, h₁⟩ else 0) - 
                     (if h₂ : i.val < m then c2.get ⟨i.val, h₂⟩ else 0)⌝⦄ := by
  simpa [hermesub, hermesubFn] using
    (by
      intro (_h : True)
      intro i
      simp [hermesubFn])
-- </vc-theorems>
