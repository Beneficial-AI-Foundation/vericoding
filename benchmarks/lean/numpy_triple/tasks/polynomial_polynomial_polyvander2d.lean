-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polyvander2d {n : Nat} (x y : Vector Float n) (xDeg yDeg : Nat) : 
    Id (Vector (Vector Float ((xDeg + 1) * (yDeg + 1))) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polyvander2d_spec {n : Nat} (x y : Vector Float n) (xDeg yDeg : Nat) :
    ⦃⌜True⌝⦄
    polyvander2d x y xDeg yDeg
    ⦃⇓V => ⌜∀ k : Fin n, ∀ i : Fin (xDeg + 1), ∀ j : Fin (yDeg + 1),
            let colIdx := (yDeg + 1) * i.val + j.val
            let colIdxFin : Fin ((xDeg + 1) * (yDeg + 1)) := 
              ⟨colIdx, by sorry⟩
            (V.get k).get colIdxFin = (x.get k) ^ (Float.ofNat i.val) * (y.get k) ^ (Float.ofNat j.val)⌝⦄ := by
  sorry
-- </vc-theorems>