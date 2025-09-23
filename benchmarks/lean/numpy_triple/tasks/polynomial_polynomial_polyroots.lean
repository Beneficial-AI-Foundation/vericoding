-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polyroots {n : Nat} (c : Vector Float (n + 1)) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polyroots_spec {n : Nat} (c : Vector Float (n + 1)) 
    (h_nonzero : c.get ⟨n, by omega⟩ ≠ 0) :
    ⦃⌜c.get ⟨n, by omega⟩ ≠ 0⌝⦄
    polyroots c
    ⦃⇓roots => ⌜∀ i : Fin n, ∃ j : Fin (n + 1), c.get j ≠ 0⌝⦄ := by
  sorry
-- </vc-theorems>