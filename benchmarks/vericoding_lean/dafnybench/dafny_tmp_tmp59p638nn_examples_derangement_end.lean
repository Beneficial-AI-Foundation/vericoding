import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- end satisfies the following properties. -/
def end (links : seq<nat>) : Id Unit :=
  sorry

/-- Specification: end satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem end_spec (links : seq<nat>) :
    ⦃⌜True⌝⦄
    end links
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
