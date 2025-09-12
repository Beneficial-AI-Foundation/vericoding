import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ComputeFusc satisfies the following properties. -/
def ComputeFusc (N : Int) : Id Unit :=
  sorry

/-- Specification: ComputeFusc satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ComputeFusc_spec (N : Int) :
    ⦃⌜True⌝⦄
    ComputeFusc N
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
