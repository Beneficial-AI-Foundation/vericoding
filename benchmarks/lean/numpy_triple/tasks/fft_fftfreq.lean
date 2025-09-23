-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fftfreq {n : Nat} (d : Float := 1.0) (h : n > 0) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fftfreq_spec {n : Nat} (d : Float) (h_n : n > 0) (h_d : d ≠ 0) :
    ⦃⌜n > 0 ∧ d ≠ 0⌝⦄
    fftfreq d h_n
    ⦃⇓result => ⌜let N := (n + 1) / 2;
                  (∀ i : Fin n, i.val < N → 
                    result.get i = Float.ofNat i.val / (Float.ofNat n * d)) ∧
                  (∀ i : Fin n, i.val ≥ N → 
                    result.get i = Float.ofInt (Int.ofNat i.val - Int.ofNat n) / (Float.ofNat n * d)) ∧
                  (result.get ⟨0, by omega⟩ = 0)⌝⦄ := by
  sorry
-- </vc-theorems>