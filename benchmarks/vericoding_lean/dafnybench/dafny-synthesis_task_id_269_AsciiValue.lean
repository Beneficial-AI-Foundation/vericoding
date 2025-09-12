import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- AsciiValue satisfies the following properties. -/
def AsciiValue (c : char) : Id Unit :=
  sorry

/-- Specification: AsciiValue satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem AsciiValue_spec (c : char) :
    ⦃⌜True⌝⦄
    AsciiValue c
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
