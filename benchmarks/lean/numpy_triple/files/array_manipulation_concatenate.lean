-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def concatenate {n m : Nat} (a : Vector Float n) (b : Vector Float m) : Id (Vector Float (n + m)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem concatenate_spec {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
    ⦃⌜True⌝⦄
    concatenate a b
    ⦃⇓result => ⌜(∀ i : Fin n, result.get ⟨i.val, by omega⟩ = a.get i) ∧
                 (∀ j : Fin m, result.get ⟨n + j.val, by omega⟩ = b.get j)⌝⦄ := by
  sorry
-- </vc-theorems>