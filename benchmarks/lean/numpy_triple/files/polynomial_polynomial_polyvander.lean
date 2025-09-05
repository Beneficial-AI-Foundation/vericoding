/-  Vandermonde matrix of given degree.
    Returns the Vandermonde matrix of degree `deg` and sample points `x`.
    The Vandermonde matrix is defined by V[i,j] = x[i]^j for 0 <= j <= deg. -/

/-  Specification: polyvander generates a Vandermonde matrix where each row corresponds to
    powers of the corresponding element in x, from degree 0 to deg. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def polyvander {n : Nat} (x : Vector Float n) (deg : Nat) : Id (Vector (Vector Float (deg + 1)) n) :=
  sorry

theorem polyvander_spec {n : Nat} (x : Vector Float n) (deg : Nat) :
    ⦃⌜True⌝⦄
    polyvander x deg
    ⦃⇓V => ⌜∀ i : Fin n, 
             (V.get i).get ⟨0, Nat.zero_lt_succ deg⟩ = 1.0 ∧ 
             (deg > 0 → (V.get i).get ⟨1, sorry⟩ = x.get i)⌝⦄ := by
  sorry
