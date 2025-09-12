import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- LinearSearch satisfies the following properties. -/
def LinearSearch (a : array<uint32>) : Id Unit :=
  sorry

/-- Specification: LinearSearch satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem LinearSearch_spec (a : array<uint32>) :
    ⦃⌜True⌝⦄
    LinearSearch a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
