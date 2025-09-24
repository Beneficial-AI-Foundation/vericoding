-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def atleast_3d {n : Nat} (arr : Vector Float n) : Id (Vector (Vector (Vector Float 1) n) 1) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem atleast_3d_spec {n : Nat} (arr : Vector Float n) :
    ⦃⌜True⌝⦄
    atleast_3d arr
    ⦃⇓result => ⌜(∀ (i : Fin n), 
                   let outer := result.get ⟨0, by simp⟩
                   let middle := outer.get i
                   let value := middle.get ⟨0, by simp⟩
                   value = arr.get i) ∧
                  (result.size = 1) ∧
                  (∀ (j : Fin 1), (result.get j).size = n) ∧
                  (∀ (j : Fin 1) (k : Fin n), ((result.get j).get k).size = 1)⌝⦄ := by
  sorry
-- </vc-theorems>