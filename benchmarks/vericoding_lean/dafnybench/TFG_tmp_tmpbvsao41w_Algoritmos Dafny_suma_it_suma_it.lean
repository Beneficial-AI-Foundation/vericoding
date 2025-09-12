import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- suma_it satisfies the following properties. -/
def suma_it (V : Array Int) : Id Unit :=
  sorry

/-- Specification: suma_it satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem suma_it_spec (V : Array Int) :
    ⦃⌜True⌝⦄
    suma_it V
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
