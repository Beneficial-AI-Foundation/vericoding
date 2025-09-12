import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- toMultiset satisfies the following properties. -/
def toMultiset (s : String) : Id Unit :=
  sorry

/-- Specification: toMultiset satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem toMultiset_spec (s : String) :
    ⦃⌜True⌝⦄
    toMultiset s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
