import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- do_algebra satisfies the following properties. -/
def do_algebra (operators : seq<char>) : Id Unit :=
  sorry

/-- Specification: do_algebra satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem do_algebra_spec (operators : seq<char>) :
    ⦃⌜True⌝⦄
    do_algebra operators
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
