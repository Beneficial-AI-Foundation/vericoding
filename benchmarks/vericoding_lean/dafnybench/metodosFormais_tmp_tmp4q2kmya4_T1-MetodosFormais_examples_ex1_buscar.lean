import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- buscar satisfies the following properties. -/
def buscar (a : Array Int) : Id Unit :=
  sorry

/-- Specification: buscar satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem buscar_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    buscar a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
