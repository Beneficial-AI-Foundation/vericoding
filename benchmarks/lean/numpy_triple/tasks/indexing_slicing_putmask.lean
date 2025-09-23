-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def putmask {n m : Nat} (a : Vector Float n) (mask : Vector Bool n) (values : Vector Float m) 
    (h : m > 0) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem putmask_spec {n m : Nat} (a : Vector Float n) (mask : Vector Bool n) (values : Vector Float m) 
    (h : m > 0) :
    ⦃⌜m > 0⌝⦄
    putmask a mask values h
    ⦃⇓result => ⌜(∀ i : Fin n, mask.get i = true → result.get i = values.get ⟨i.val % m, Nat.mod_lt i.val h⟩) ∧
                (∀ i : Fin n, mask.get i = false → result.get i = a.get i) ∧
                (∀ i : Fin n, mask.get i = true → ∃ j : Fin m, result.get i = values.get j)⌝⦄ := by
  sorry
-- </vc-theorems>