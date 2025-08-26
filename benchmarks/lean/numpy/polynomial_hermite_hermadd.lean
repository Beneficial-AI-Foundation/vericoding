import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.polynomial.hermite.hermadd: Add one Hermite series to another.

    Returns the sum of two Hermite series c1 + c2. The arguments are
    sequences of coefficients ordered from lowest order term to highest,
    i.e., [1,2,3] represents the series P_0 + 2*P_1 + 3*P_2.

    Unlike multiplication, division, etc., the sum of two Hermite series
    is a Hermite series (without having to "reproject" the result onto
    the basis set) so addition, just like that of "standard" polynomials,
    is simply "component-wise."

    This version handles adding two Hermite coefficient vectors where the
    result length is the maximum of the input lengths. Shorter vectors are
    implicitly padded with zeros.
-/
def hermadd {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : 
    Id (Vector Float (max n m)) :=
  sorry

/-- Specification: hermadd performs component-wise addition of Hermite series coefficients.

    Precondition: True (no special preconditions for basic addition)
    Postcondition: 
    - If i < min(n,m), result[i] = c1[i] + c2[i]
    - If min(n,m) ≤ i < n, result[i] = c1[i] (c2 is treated as 0)
    - If min(n,m) ≤ i < m, result[i] = c2[i] (c1 is treated as 0)
    
    The mathematical property: The i-th coefficient of the sum is the sum of
    the i-th coefficients of the input series, treating missing coefficients as 0.
-/
theorem hermadd_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) :
    ⦃⌜True⌝⦄
    hermadd c1 c2
    ⦃⇓result => ⌜∀ i : Fin (max n m), 
                  result.get i = 
                    if h1 : i.val < n then
                      if h2 : i.val < m then
                        c1.get ⟨i.val, h1⟩ + c2.get ⟨i.val, h2⟩
                      else
                        c1.get ⟨i.val, h1⟩
                    else
                      if h2 : i.val < m then
                        c2.get ⟨i.val, h2⟩
                      else
                        0⌝⦄ := by
  sorry