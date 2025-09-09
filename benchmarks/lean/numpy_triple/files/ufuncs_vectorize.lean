import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def vectorize {n : Nat} {α β : Type} (f : α → β) (arr : Vector α n) : Id (Vector β n) :=
  sorry

theorem vectorize_spec {n : Nat} {α β : Type} (f : α → β) (arr : Vector α n) :
    ⦃⌜True⌝⦄
    vectorize f arr
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = f (arr.get i)⌝⦄ := by
  sorry
