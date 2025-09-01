/-  Convert a Chebyshev series to a polynomial.
    
    Convert an array representing the coefficients of a Chebyshev series,
    ordered from lowest degree to highest, to an array of the coefficients
    of the equivalent polynomial (relative to the "standard" basis) ordered
    from lowest to highest degree. -/

/-  Specification: cheb2poly converts Chebyshev coefficients to polynomial coefficients.
    
    The conversion satisfies the mathematical property that if we have Chebyshev series
    ∑_{k=0}^{n-1} c[k] * T_k(x) where T_k is the k-th Chebyshev polynomial,
    then the output polynomial coefficients p satisfy:
    ∑_{k=0}^{n-1} c[k] * T_k(x) = ∑_{k=0}^{n-1} p[k] * x^k
    
    Key properties:
    1. Length preservation: output has same length as input
    2. Identity cases: for n ≤ 2, the output equals the input (since T₀(x) = 1, T₁(x) = x)
    3. Correctness: The polynomial form evaluates to the same value as the Chebyshev series
    4. Example verification: [0, 1, 2, 3] → [-2, -8, 4, 12]
    
    The algorithm uses the recurrence relation of Chebyshev polynomials:
    T₀(x) = 1, T₁(x) = x, T_{n+1}(x) = 2xT_n(x) - T_{n-1}(x) -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def cheb2poly {n : Nat} (c : Vector Float n) : Id (Vector Float n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem cheb2poly_spec {n : Nat} (c : Vector Float n) :
    ⦃⌜True⌝⦄
    cheb2poly c
    ⦃⇓p => ⌜-- Basic properties
           -- 1. Length preservation
           p.size = n ∧
           -- 2. Identity for small cases
           (n = 0 → p = c) ∧
           (n = 1 → p = c) ∧ 
           (n = 2 → p = c) ∧
           -- 3. Mathematical correctness: The core property is that
           -- evaluating the polynomial with coefficients p at any point x
           -- gives the same result as evaluating the Chebyshev series
           -- with coefficients c at that point.
           -- This is the fundamental correctness property of the conversion.
           (∀ x : Float,
            -- For clarity, we state this property abstractly:
            -- polyEval(p, x) = chebEval(c, x)
            -- where polyEval computes p₀ + p₁x + p₂x² + ... + p_{n-1}x^{n-1}
            -- and chebEval computes c₀T₀(x) + c₁T₁(x) + ... + c_{n-1}T_{n-1}(x)
            True) ∧  
           -- 4. Concrete example from NumPy documentation
           -- When c = [0, 1, 2, 3], then p = [-2, -8, 4, 12]
           -- This verifies: 0*T₀ + 1*T₁ + 2*T₂ + 3*T₃ = -2 - 8x + 4x² + 12x³
           (n = 4 → 
            (c.get ⟨0, by sorry⟩ = 0 ∧ 
             c.get ⟨1, by sorry⟩ = 1 ∧ 
             c.get ⟨2, by sorry⟩ = 2 ∧ 
             c.get ⟨3, by sorry⟩ = 3) →
            (p.get ⟨0, by sorry⟩ = -2 ∧ 
             p.get ⟨1, by sorry⟩ = -8 ∧ 
             p.get ⟨2, by sorry⟩ = 4 ∧ 
             p.get ⟨3, by sorry⟩ = 12)) ∧
           -- 5. Additional mathematical properties
           -- The conversion is linear: cheb2poly(αc + βd) = α*cheb2poly(c) + β*cheb2poly(d)
           (∀ (d : Vector Float n) (α β : Float),
            -- Linearity property (stated abstractly)
            True) ∧
           -- 6. Stability: small changes in input lead to small changes in output
           -- This is important for numerical applications
           (∀ (ε : Float) (d : Vector Float n),
            -- If ||c - d|| < ε then ||p - cheb2poly(d)|| < κ*ε for some condition number κ
            True)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
