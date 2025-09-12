import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MinLengthSublist satisfies the following properties. -/
def MinLengthSublist (s : seq<seq<int>>) : Id Unit :=
  sorry

/-- Specification: MinLengthSublist satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MinLengthSublist_spec (s : seq<seq<int>>) :
    ⦃⌜True⌝⦄
    MinLengthSublist s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
