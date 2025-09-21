-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermeline (off scl : Float) : Id (Vector Float 2) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermeline_spec (off scl : Float) :
    ⦃⌜True⌝⦄
    hermeline off scl
    ⦃⇓coeffs => ⌜-- Core structural property: always returns exactly 2 coefficients
                  coeffs.size = 2 ∧ 
                  -- Constant term property: first coefficient is always the offset
                  coeffs.get ⟨0, by simp⟩ = off ∧
                  -- Linear term property: second coefficient depends on scale
                  (scl = 0 → coeffs.get ⟨1, by simp⟩ = 0) ∧
                  (scl ≠ 0 → coeffs.get ⟨1, by simp⟩ = scl) ∧
                  -- Mathematical consistency: coefficients represent off + scl*x
                  (∀ x : Float, 
                    let polynomial_value := coeffs.get ⟨0, by simp⟩ + coeffs.get ⟨1, by simp⟩ * x
                    polynomial_value = off + scl * x) ∧
                  -- Degenerate case property: zero scale gives constant polynomial
                  (scl = 0 → ∀ x : Float, 
                    coeffs.get ⟨0, by simp⟩ + coeffs.get ⟨1, by simp⟩ * x = off) ∧
                  -- Non-degenerate case property: non-zero scale gives linear polynomial
                  (scl ≠ 0 → ∀ x : Float, 
                    coeffs.get ⟨0, by simp⟩ + coeffs.get ⟨1, by simp⟩ * x = off + scl * x)⌝⦄ := by
  sorry
-- </vc-theorems>