import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FooCount satisfies the following properties. -/
def FooCount (CountIndex : Nat) : Id Unit :=
  sorry

/-- Specification: FooCount satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FooCount_spec (CountIndex : Nat) :
    ⦃⌜True⌝⦄
    FooCount CountIndex
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
