-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def vector_norm {n : Nat} (x : Vector Float n) (p : Float) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vector_norm_spec {n : Nat} (x : Vector Float n) (p : Float) 
    (h_valid_p : p ≥ 0) :
    ⦃⌜p ≥ 0⌝⦄
    vector_norm x p
    ⦃⇓result => ⌜result ≥ 0 ∧
                 (n = 0 → result = 0) ∧
                 (p = 2 → result = Float.sqrt (List.sum (x.toList.map (fun xi => xi * xi)))) ∧
                 (p = 1 → result = List.sum (x.toList.map (fun xi => Float.abs xi))) ∧
                 (p = 0 → result = Float.ofNat (x.toList.filter (fun xi => xi != 0)).length) ∧
                 (p > 1 → 
                   result = Float.pow (List.sum (x.toList.map (fun xi => Float.pow (Float.abs xi) p))) (1 / p)) ∧
                 (result = 0 ↔ (p > 0 ∧ ∀ i : Fin n, x.get i = 0))⌝⦄ := by
  sorry
-- </vc-theorems>