-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multi_dot {n₁ n₂ n₃ n₄ : Nat} 
    (A : Vector (Vector Float n₂) n₁) 
    (B : Vector (Vector Float n₃) n₂) 
    (C : Vector (Vector Float n₄) n₃) : 
    Id (Vector (Vector Float n₄) n₁) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multi_dot_spec {n₁ n₂ n₃ n₄ : Nat} 
    (A : Vector (Vector Float n₂) n₁) 
    (B : Vector (Vector Float n₃) n₂) 
    (C : Vector (Vector Float n₄) n₃) :
    ⦃⌜True⌝⦄
    multi_dot A B C
    ⦃⇓result => ⌜result.toList.length = n₁ ∧ 
                  ∀ i : Fin n₁, (result.get i).toList.length = n₄ ∧
                  ∀ i : Fin n₁, ∀ j : Fin n₄, 
                    ∃ matrix_product : Float,
                    (result.get i).get j = matrix_product ∧ 
                    matrix_product = List.sum (List.zipWith (· * ·) 
                      (A.get i).toList 
                      (List.map (fun row => 
                        List.sum (List.zipWith (· * ·) 
                          row.toList 
                          (List.map (fun col => col.get j) C.toList))) 
                        B.toList))⌝⦄ := by
  sorry
-- </vc-theorems>