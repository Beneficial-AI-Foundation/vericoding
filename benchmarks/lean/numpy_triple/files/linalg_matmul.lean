import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def matmul {m n p : Nat} (A : Vector (Vector Float n) m) (B : Vector (Vector Float p) n) : 
    Id (Vector (Vector Float p) m) :=
  sorry

theorem matmul_spec {m n p : Nat} (A : Vector (Vector Float n) m) (B : Vector (Vector Float p) n) :
    ⦃⌜True⌝⦄
    matmul A B
    ⦃⇓C => ⌜∀ i : Fin m, ∀ j : Fin p, 
              (C.get i).get j = List.sum (List.zipWith (· * ·) 
                (A.get i).toList 
                (List.map (fun row => row.get j) B.toList))⌝⦄ := by
  sorry
