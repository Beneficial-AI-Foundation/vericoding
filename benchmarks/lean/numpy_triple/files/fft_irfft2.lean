-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_irfft2 {rows cols : Nat} (a : Vector (Vector Float cols) rows) : Id (Vector (Vector Float cols) rows) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_irfft2_spec {rows cols : Nat} (a : Vector (Vector Float cols) rows) :
    ⦃⌜True⌝⦄
    numpy_irfft2 a
    ⦃⇓result => ⌜-- Preserve matrix dimensions
      (∀ i : Fin rows, (result.get i).size = cols) ∧
      -- Output is well-formed  
      result.size = rows ∧
      -- All elements are processed and produce finite values
      (∀ i : Fin rows, ∀ j : Fin cols, 
        ((result.get i).get j).isFinite) ∧
      -- Non-trivial transformation: if input is non-zero, result depends on input
      (∀ i : Fin rows, ∀ j : Fin cols,
        (a.get i).get j ≠ 0 → 
        ∃ (k : Fin rows) (l : Fin cols), (result.get k).get l ≠ 0)⌝⦄ := by
  sorry
-- </vc-theorems>