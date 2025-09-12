import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Exchanger satisfies the following properties. -/
def Exchanger (s : seq<Bases>) : Id Unit :=
  sorry

/-- Specification: Exchanger satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Exchanger_spec (s : seq<Bases>) :
    ⦃⌜True⌝⦄
    Exchanger s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
