import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- GetValor satisfies the following properties. -/
def GetValor (v : Int) : Id Unit :=
  sorry

/-- Specification: GetValor satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem GetValor_spec (v : Int) :
    ⦃⌜True⌝⦄
    GetValor v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
