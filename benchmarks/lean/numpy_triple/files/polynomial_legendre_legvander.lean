/-  Pseudo-Vandermonde matrix of given degree based on Legendre polynomials.
    Returns the pseudo-Vandermonde matrix of degree `deg` and sample points `x`.
    The pseudo-Vandermonde matrix is defined by V[..., i] = L_i(x) where 0 <= i <= deg.
    L_i represents the i-th Legendre polynomial. -/

/-  Specification: legvander constructs a pseudo-Vandermonde matrix where each row 
    corresponds to a point and each column corresponds to a Legendre polynomial evaluation.
    The matrix satisfies basic properties of Legendre polynomials:
    - L_0(x) = 1 (first column is all ones)
    - L_1(x) = x (second column equals input values when deg > 0)
    - The matrix has the correct dimensions -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def legvander {n : Nat} (x : Vector Float n) (deg : Nat) : Id (Vector (Vector Float (deg + 1)) n) :=
  sorry

theorem legvander_spec {n : Nat} (x : Vector Float n) (deg : Nat) :
    ⦃⌜True⌝⦄
    legvander x deg
    ⦃⇓result => ⌜
      -- First column (L_0) is all ones
      (∀ i : Fin n, (result.get i).get ⟨0, Nat.zero_lt_succ deg⟩ = 1) ∧
      -- Second column (L_1) equals x values when deg > 0
      (deg > 0 → ∀ i : Fin n, (result.get i).get ⟨1, sorry⟩ = x.get i) ∧
      -- Matrix has correct dimensions and well-defined values
      (∀ i : Fin n, ∀ j : Fin (deg + 1), ∃ val : Float, (result.get i).get j = val)
    ⌝⦄ := by
  sorry
