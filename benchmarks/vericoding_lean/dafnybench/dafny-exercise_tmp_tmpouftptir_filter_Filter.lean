import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Filter satisfies the following properties. -/
def Filter (a : seq<char>) : Id Unit :=
  sorry

/-- Specification: Filter satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Filter_spec (a : seq<char>) :
    ⦃⌜True⌝⦄
    Filter a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
