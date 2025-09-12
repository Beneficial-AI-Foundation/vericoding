import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- rev satisfies the following properties. -/
def rev (a : Array Int) : Id Unit :=
  sorry

/-- Specification: rev satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem rev_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    rev a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
