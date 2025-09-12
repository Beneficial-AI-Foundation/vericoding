import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- suma_componentes satisfies the following properties. -/
def suma_componentes (V : array?<int>) : Id Unit :=
  sorry

/-- Specification: suma_componentes satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem suma_componentes_spec (V : array?<int>) :
    ⦃⌜True⌝⦄
    suma_componentes V
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
