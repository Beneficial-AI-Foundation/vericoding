-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_append {n m : Nat} (arr : Vector Float n) (values : Vector Float m) : 
    Id (Vector Float (n + m)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_append_spec {n m : Nat} (arr : Vector Float n) (values : Vector Float m) :
    ⦃⌜True⌝⦄
    numpy_append arr values
    ⦃⇓result => ⌜(∀ i : Fin n, result.get (i.castAdd m) = arr.get i) ∧
                (∀ j : Fin m, result.get (j.natAdd n) = values.get j)⌝⦄ := by
  sorry
-- </vc-theorems>