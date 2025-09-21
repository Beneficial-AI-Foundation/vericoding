-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def meshgrid {m n : Nat} (x : Vector Float m) (y : Vector Float n) : 
    Id (Vector (Vector Float m) n × Vector (Vector Float m) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem meshgrid_spec {m n : Nat} (x : Vector Float m) (y : Vector Float n) :
    ⦃⌜True⌝⦄
    meshgrid x y
    ⦃⇓result => 
      let (xv, yv) := result
      ⌜-- First matrix: x values repeated along each row
       (∀ i : Fin n, ∀ j : Fin m, (xv.get i).get j = x.get j) ∧
       -- Second matrix: y values repeated along each column  
       (∀ i : Fin n, ∀ j : Fin m, (yv.get i).get j = y.get i)⌝⦄ := by
  sorry
-- </vc-theorems>