-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermadd {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : 
    Id (Vector Float (max n m)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermadd_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) :
    ⦃⌜True⌝⦄
    hermadd c1 c2
    ⦃⇓result => ⌜∀ i : Fin (max n m), 
                  result.get i = 
                    if h1 : i.val < n then
                      if h2 : i.val < m then
                        c1.get ⟨i.val, h1⟩ + c2.get ⟨i.val, h2⟩
                      else
                        c1.get ⟨i.val, h1⟩
                    else
                      if h2 : i.val < m then
                        c2.get ⟨i.val, h2⟩
                      else
                        0⌝⦄ := by
  sorry
-- </vc-theorems>