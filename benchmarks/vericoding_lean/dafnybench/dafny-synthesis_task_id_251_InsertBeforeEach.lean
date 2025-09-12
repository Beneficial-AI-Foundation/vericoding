import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- InsertBeforeEach satisfies the following properties. -/
def InsertBeforeEach (s : seq<string>) : Id Unit :=
  sorry

/-- Specification: InsertBeforeEach satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem InsertBeforeEach_spec (s : seq<string>) :
    ⦃⌜True⌝⦄
    InsertBeforeEach s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
