import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- GetTriple satisfies the following properties. -/
def GetTriple (a : Array Int) : Id Unit :=
  sorry

/-- Specification: GetTriple satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem GetTriple_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    GetTriple a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
