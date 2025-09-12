import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- query satisfies the following properties. -/
def query (a : Array Int) : Id Unit :=
  sorry

/-- Specification: query satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem query_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    query a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
