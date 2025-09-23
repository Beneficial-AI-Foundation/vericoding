-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ogrid {n : Nat} (start stop : Float) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ogrid_spec {n : Nat} (start stop : Float) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    ogrid start stop
    ⦃⇓result => ⌜-- For a single element, it equals start
                (n = 1 → result.get ⟨0, h⟩ = start) ∧
                -- For multiple elements, they are evenly spaced from start to stop
                (∀ i : Fin n, 
                  n > 1 → result.get i = start + i.val.toFloat * ((stop - start) / (n - 1).toFloat)) ∧
                -- Boundary conditions
                (n > 1 → result.get ⟨0, h⟩ = start ∧ 
                         result.get ⟨n - 1, Nat.sub_lt h (Nat.zero_lt_one)⟩ = stop)⌝⦄ := by
  sorry
-- </vc-theorems>