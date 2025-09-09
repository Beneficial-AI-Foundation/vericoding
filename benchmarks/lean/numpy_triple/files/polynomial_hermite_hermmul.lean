/-  numpy.polynomial.hermite.hermmul: Multiply one Hermite series by another.

    Returns the product of two Hermite series c1 * c2. The arguments
    are sequences of coefficients, from lowest order term to highest,
    e.g., [1,2,3] represents the series P_0 + 2*P_1 + 3*P_2 where P_i
    is the i-th Hermite polynomial.

    The product of two Hermite series requires reprojection onto the
    Hermite basis, which uses the recurrence relation for Hermite
    polynomials.

    For non-empty inputs of length m and n, the result has length m + n - 1.
    For empty inputs, returns a single zero coefficient.
-/

/-  Specification: hermmul returns the coefficients of the product of two
    Hermite series.

    The key mathematical properties:
    1. Empty input handling: If either input is empty, returns [0]
    2. Degree property: For non-empty inputs of degree m-1 and n-1,
       the product has degree (m-1) + (n-1) = m + n - 2, requiring m + n - 1 coefficients
    3. Multiplication by constant: When one series has only one coefficient (constant polynomial),
       the result is element-wise scaling
    4. Commutativity: hermmul c1 c2 = hermmul c2 c1 (up to floating point precision)
    5. The general multiplication follows Hermite polynomial recurrence relations

    Precondition: True (works for all valid inputs)
    Postcondition: Captures empty input behavior, constant multiplication, and size properties
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def hermmul (m n : Nat) (c1 : Vector Float m) (c2 : Vector Float n) : 
    Id (Vector Float (if m = 0 ∨ n = 0 then 1 else m + n - 1)) :=
  sorry

theorem hermmul_spec (m n : Nat) (c1 : Vector Float m) (c2 : Vector Float n) :
    ⦃⌜True⌝⦄
    hermmul m n c1 c2
    ⦃⇓result => ⌜
      -- Empty input handling
      ((m = 0 ∨ n = 0) → result.size = 1 ∧ result.get ⟨0, sorry⟩ = 0) ∧
      -- Non-empty inputs have correct output size
      (m > 0 ∧ n > 0 → result.size = m + n - 1) ∧
      -- Multiplication by constant polynomial (degree 0)
      (n = 1 ∧ m > 0 → ∀ i : Fin m, 
        result.get ⟨i.val, sorry⟩ = c1.get i * c2.get ⟨0, sorry⟩) ∧
      (m = 1 ∧ n > 0 → ∀ i : Fin n, 
        result.get ⟨i.val, sorry⟩ = c2.get i * c1.get ⟨0, sorry⟩) ∧
      -- Zero polynomial property
      ((∀ i : Fin m, c1.get i = 0) ∨ (∀ j : Fin n, c2.get j = 0) → 
        ∀ k : Fin result.size, result.get k = 0)
    ⌝⦄ := by
  sorry
