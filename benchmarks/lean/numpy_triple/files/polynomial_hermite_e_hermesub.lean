import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def hermesub {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : Id (Vector Float (max n m)) :=
  sorry

theorem hermesub_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) :
    ⦃⌜True⌝⦄
    hermesub c1 c2
    ⦃⇓result => ⌜∀ i : Fin (max n m), 
      result.get i = (if h₁ : i.val < n then c1.get ⟨i.val, h₁⟩ else 0) - 
                     (if h₂ : i.val < m then c2.get ⟨i.val, h₂⟩ else 0)⌝⦄ := by
  sorry
