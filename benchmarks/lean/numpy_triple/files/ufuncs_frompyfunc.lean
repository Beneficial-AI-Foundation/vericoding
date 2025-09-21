-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_frompyfunc {α β : Type} {n : Nat} (func : α → β) (input : Vector α n) : Id (Vector β n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_frompyfunc_spec {α β : Type} {n : Nat} (func : α → β) (input : Vector α n) :
    ⦃⌜True⌝⦄
    numpy_frompyfunc func input
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = func (input.get i)⌝⦄ := by
  sorry
-- </vc-theorems>