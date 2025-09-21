-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def var {n : Nat} (a : Vector Float (n + 1)) (ddof : Nat) (h : ddof < n + 1) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem var_spec {n : Nat} (a : Vector Float (n + 1)) (ddof : Nat) (h : ddof < n + 1) :
    ⦃⌜ddof < n + 1⌝⦄
    var a ddof h
    ⦃⇓result => ⌜result ≥ 0 ∧
                 (result = 0 ↔ ∀ i j : Fin (n + 1), a.get i = a.get j) ∧
                 (∀ (c : Float), ∀ (b : Vector Float (n + 1)), 
                   (∀ i : Fin (n + 1), b.get i = a.get i + c) → 
                   var b ddof h = result) ∧
                 (∀ (c : Float), c ≠ 0 → ∀ (b : Vector Float (n + 1)), 
                   (∀ i : Fin (n + 1), b.get i = c * a.get i) → 
                   var b ddof h = c^2 * result)⌝⦄ := by
  sorry
-- </vc-theorems>