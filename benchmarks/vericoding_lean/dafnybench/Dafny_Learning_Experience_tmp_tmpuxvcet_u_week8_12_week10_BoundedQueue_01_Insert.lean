import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Insert satisfies the following properties. -/
def Insert (x : T) : Id Unit :=
  sorry

/-- Specification: Insert satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Insert_spec (x : T) :
    ⦃⌜True⌝⦄
    Insert x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
