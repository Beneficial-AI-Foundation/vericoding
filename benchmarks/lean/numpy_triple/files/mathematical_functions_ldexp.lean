/- 
{
  "name": "numpy.ldexp",
  "description": "Returns x1 * 2**x2, element-wise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ldexp.html",
  "doc": "Returns x1 * 2**x2, element-wise.\n\nThe mantissas x1 and twos exponents x2 are used to construct floating point numbers x1 * 2**x2.",
}
-/

/-  Returns x1 * 2**x2, element-wise.
    The mantissas x1 and twos exponents x2 are used to construct floating point numbers x1 * 2**x2. -/

/-  Specification: ldexp returns x1 * 2**x2 element-wise -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def ldexp {n : Nat} (x1 : Vector Float n) (x2 : Vector Int n) : Id (Vector Float n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem ldexp_spec {n : Nat} (x1 : Vector Float n) (x2 : Vector Int n) :
    ⦃⌜True⌝⦄
    ldexp x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i * (2 : Float) ^ (Float.ofInt (x2.get i))⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
