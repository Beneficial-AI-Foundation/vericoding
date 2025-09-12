import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- insert satisfies the following properties. -/
def insert (line : array<char>) : Id Unit :=
  sorry

/-- Specification: insert satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem insert_spec (line : array<char>) :
    ⦃⌜True⌝⦄
    insert line
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
