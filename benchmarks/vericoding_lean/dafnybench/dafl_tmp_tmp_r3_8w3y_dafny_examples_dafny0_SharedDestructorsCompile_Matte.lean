import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Matte satisfies the following properties. -/
def Matte (d : Datte<real>) : Id Unit :=
  sorry

/-- Specification: Matte satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Matte_spec (d : Datte<real>) :
    ⦃⌜True⌝⦄
    Matte d
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
