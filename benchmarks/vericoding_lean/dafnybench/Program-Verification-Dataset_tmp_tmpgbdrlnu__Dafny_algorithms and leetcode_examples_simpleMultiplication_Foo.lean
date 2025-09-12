import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Foo satisfies the following properties. -/
def Foo (y : Int) : Id Unit :=
  sorry

/-- Specification: Foo satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Foo_spec (y : Int) :
    ⦃⌜True⌝⦄
    Foo y
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
