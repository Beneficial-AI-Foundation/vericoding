/-  Evaluate a polynomial specified by its roots at points x.
    If `r` is of length `N`, this function returns the value p(x) = ∏(x - r_i)
    where the product is over all roots r_i in the roots vector. -/

/-  Specification: polyvalfromroots evaluates the polynomial with the given roots
    at each point in x. The polynomial is defined as the product of (x - r_i) for all roots r_i. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def polyvalfromroots {n m : Nat} (x : Vector Float n) (r : Vector Float m) : Id (Vector Float n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem polyvalfromroots_spec {n m : Nat} (x : Vector Float n) (r : Vector Float m) :
    ⦃⌜True⌝⦄
    polyvalfromroots x r
    ⦃⇓result => ⌜∀ i : Fin n, 
                  result.get i = (List.range m).foldl (fun acc j => acc * (x.get i - r.get ⟨j, sorry⟩)) 1⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
