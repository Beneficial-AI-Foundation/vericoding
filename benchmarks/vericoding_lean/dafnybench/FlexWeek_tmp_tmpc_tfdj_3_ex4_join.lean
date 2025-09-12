import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- join satisfies the following properties. -/
def join (a : Array Int) : Id Unit :=
  sorry

/-- Specification: join satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem join_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    join a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
