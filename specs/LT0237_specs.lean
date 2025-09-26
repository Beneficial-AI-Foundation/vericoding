-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def norm {n : Nat} (x : Vector Float n) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem norm_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    norm x
    ⦃⇓result => ⌜result = Float.sqrt (List.sum (x.toList.map (fun xi => xi * xi))) ∧
                 result ≥ 0 ∧
                 (result = 0 ↔ ∀ i : Fin n, x.get i = 0) ∧
                 (n = 0 → result = 0)⌝⦄ := by
  sorry
-- </vc-theorems>