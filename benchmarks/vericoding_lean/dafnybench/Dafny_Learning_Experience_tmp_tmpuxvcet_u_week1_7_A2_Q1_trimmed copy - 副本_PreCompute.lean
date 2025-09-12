import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ComputeCount satisfies the following properties. -/
def ComputeCount (CountIndex : Nat) : Id Unit :=
  sorry

/-- Specification: ComputeCount satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ComputeCount_spec (CountIndex : Nat) :
    ⦃⌜True⌝⦄
    ComputeCount CountIndex
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
