-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polyvander3d {n : Nat} (x y z : Vector Float n) (xDeg yDeg zDeg : Nat) : 
    Id (Vector (Vector Float ((xDeg + 1) * (yDeg + 1) * (zDeg + 1))) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polyvander3d_spec {n : Nat} (x y z : Vector Float n) (xDeg yDeg zDeg : Nat) :
    ⦃⌜True⌝⦄
    polyvander3d x y z xDeg yDeg zDeg
    ⦃⇓V => ⌜∀ p : Fin n, ∀ i : Fin (xDeg + 1), ∀ j : Fin (yDeg + 1), ∀ k : Fin (zDeg + 1),
            let colIdx := (yDeg + 1) * (zDeg + 1) * i.val + (zDeg + 1) * j.val + k.val
            let colIdxFin : Fin ((xDeg + 1) * (yDeg + 1) * (zDeg + 1)) := 
              ⟨colIdx, by sorry⟩
            (V.get p).get colIdxFin = (x.get p) ^ (Float.ofNat i.val) * (y.get p) ^ (Float.ofNat j.val) * (z.get p) ^ (Float.ofNat k.val)⌝⦄ := by
  sorry
-- </vc-theorems>