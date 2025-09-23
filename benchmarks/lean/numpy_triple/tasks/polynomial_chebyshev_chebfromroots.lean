-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Evaluate the k-th Chebyshev polynomial of the first kind at x -/
def evalChebyshevT (k : Nat) (x : Float) : Float :=
  match k with
  | 0 => 1
  | 1 => x
  | k + 2 => 2 * x * evalChebyshevT (k + 1) x - evalChebyshevT k x
/-- Evaluate a polynomial in Chebyshev basis at point x given coefficients -/
def evalChebyshevPoly {n : Nat} (coeffs : Vector Float n) (x : Float) : Float :=
  let rec sumTerms (i : Nat) (acc : Float) : Float :=
    if h : i < n then
      sumTerms (i + 1) (acc + coeffs.get ⟨i, h⟩ * evalChebyshevT i x)
    else
      acc
  sumTerms 0 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chebfromroots {n : Nat} (roots : Vector Float n) : Id (Vector Float (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chebfromroots_spec {n : Nat} (roots : Vector Float n) :
    ⦃⌜True⌝⦄
    chebfromroots roots
    ⦃⇓coeffs => ⌜
      -- The polynomial degree matches the number of roots
      (n > 0 → coeffs.get ⟨n, by omega⟩ ≠ 0) ∧
      -- For each root r, evaluating the Chebyshev polynomial at r gives zero
      -- (This captures that the roots are indeed roots of the polynomial)
      (∀ i : Fin n, 
        evalChebyshevPoly coeffs (roots.get i) = 0) ∧
      -- Additional property: coefficient vector has the correct mathematical relationship
      -- The leading coefficient relates to the product form of the polynomial
      (n > 0 → 
        -- For a monic polynomial in standard basis, the leading coefficient would be 1,
        -- but in Chebyshev basis it's 2^(1-n) for n > 0
        coeffs.get ⟨n, by omega⟩ = Float.pow 2 (Float.ofNat (1 - n)))
    ⌝⦄ := by
  sorry
-- </vc-theorems>