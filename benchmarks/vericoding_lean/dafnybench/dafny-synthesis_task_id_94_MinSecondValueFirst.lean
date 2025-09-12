import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MinSecondValueFirst satisfies the following properties. -/
def MinSecondValueFirst (s : array<seq<int>>) : Id Unit :=
  sorry

/-- Specification: MinSecondValueFirst satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MinSecondValueFirst_spec (s : array<seq<int>>) :
    ⦃⌜True⌝⦄
    MinSecondValueFirst s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
