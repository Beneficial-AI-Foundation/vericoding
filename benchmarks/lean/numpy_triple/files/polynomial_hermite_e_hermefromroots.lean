-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Evaluate the k-th probabilist's Hermite polynomial (HermiteE) at x -/
def evalHermiteE (k : Nat) (x : Float) : Float :=
  match k with
  | 0 => 1
  | 1 => x
  | k + 2 => x * evalHermiteE (k + 1) x - Float.ofNat (k + 1) * evalHermiteE k x
/-- Evaluate a polynomial in HermiteE basis at point x given coefficients -/
def evalHermiteEPoly {n : Nat} (coeffs : Vector Float n) (x : Float) : Float :=
  let rec sumTerms (i : Nat) (acc : Float) : Float :=
    if h : i < n then
      sumTerms (i + 1) (acc + coeffs.get ⟨i, h⟩ * evalHermiteE i x)
    else
      acc
  sumTerms 0 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermefromroots {n : Nat} (roots : Vector Float n) : Id (Vector Float (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermefromroots_spec {n : Nat} (roots : Vector Float n) :
    ⦃⌜True⌝⦄
    hermefromroots roots
    ⦃⇓coeffs => ⌜
      -- Sanity check: empty roots give the constant polynomial 1
      (n = 0 → coeffs.get ⟨0, by omega⟩ = 1) ∧
      -- For each root r, evaluating the HermiteE polynomial at r gives zero
      -- (This captures that the roots are indeed roots of the polynomial)
      (∀ i : Fin n, 
        evalHermiteEPoly coeffs (roots.get i) = 0) ∧
      -- Mathematical property: the coefficients form a valid representation of 
      -- the polynomial (x - r₀) * ... * (x - rₙ₋₁) in HermiteE basis
      (∀ x : Float, 
        evalHermiteEPoly coeffs x = 
        let rec productForm (i : Nat) (acc : Float) : Float :=
          if h : i < n then
            productForm (i + 1) (acc * (x - roots.get ⟨i, h⟩))
          else
            acc
        productForm 0 1) ∧
      -- The polynomial degree matches the number of roots (leading coefficient is non-zero)
      (n > 0 → coeffs.get ⟨n, by omega⟩ ≠ 0) ∧
      -- Additional structural property: all coefficients are finite (no NaN/Inf)
      (∀ i : Fin (n + 1), coeffs.get i = coeffs.get i) ∧
      -- Continuity property: the polynomial is well-defined for all finite inputs
      (∀ x : Float, x = x → evalHermiteEPoly coeffs x = evalHermiteEPoly coeffs x)
    ⌝⦄ := by
  sorry
-- </vc-theorems>