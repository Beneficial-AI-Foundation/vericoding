import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Quotient satisfies the following properties. -/
def Quotient (a : Int) : Id Unit :=
  sorry

/-- Specification: Quotient satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Quotient_spec (a : Int) :
    ⦃⌜True⌝⦄
    Quotient a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
