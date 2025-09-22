-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_empty_like {n : Nat} (prototype : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_empty_like_spec {n : Nat} (prototype : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_empty_like prototype
    ⦃⇓result => ⌜result.size = prototype.size ∧ 
                 result.size = n ∧
                 (∀ i : Fin n, ∃ v : Float, result.get i = v) ∧
                 (∀ i : Fin prototype.size, ∃ j : Fin result.size, i.val = j.val)⌝⦄ := by
  sorry
-- </vc-theorems>