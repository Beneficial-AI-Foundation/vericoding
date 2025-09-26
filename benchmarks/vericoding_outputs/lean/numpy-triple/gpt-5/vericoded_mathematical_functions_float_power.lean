import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
attribute [simp] Vector.get_ofFn
-- </vc-helpers>

-- <vc-definitions>
def float_power {n : Nat} (base : Vector Float n) (exponent : Vector Float n) : Id (Vector Float n) :=
  pure <| Vector.ofFn (fun i => (base.get i) ^ (exponent.get i))
-- </vc-definitions>

-- <vc-theorems>
theorem float_power_spec {n : Nat} (base : Vector Float n) (exponent : Vector Float n) 
    (h_valid : ∀ i : Fin n, (base.get i > 0) ∨ (base.get i = 0 ∧ exponent.get i ≥ 0)) :
    ⦃⌜∀ i : Fin n, (base.get i > 0) ∨ (base.get i = 0 ∧ exponent.get i ≥ 0)⌝⦄
    float_power base exponent
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (base.get i) ^ (exponent.get i)⌝⦄ := by
  simpa [float_power] using
    (fun (_h : ∀ i : Fin n, (base.get i > 0) ∨ (base.get i = 0 ∧ exponent.get i ≥ 0)) =>
      by
        intro i
        simp)
-- </vc-theorems>
