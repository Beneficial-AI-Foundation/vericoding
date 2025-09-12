import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- add satisfies the following properties. -/
def add (m : Message) : Id Unit :=
  sorry

/-- Specification: add satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem add_spec (m : Message) :
    ⦃⌜True⌝⦄
    add m
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
