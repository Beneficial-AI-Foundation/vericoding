import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Hash satisfies the following properties. -/
def Hash (s : String) : Id Unit :=
  sorry

/-- Specification: Hash satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Hash_spec (s : String) :
    ⦃⌜True⌝⦄
    Hash s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
