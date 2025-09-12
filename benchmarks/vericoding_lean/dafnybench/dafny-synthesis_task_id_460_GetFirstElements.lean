import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- GetFirstElements satisfies the following properties. -/
def GetFirstElements (lst : seq<seq<int>>) : Id Unit :=
  sorry

/-- Specification: GetFirstElements satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem GetFirstElements_spec (lst : seq<seq<int>>) :
    ⦃⌜True⌝⦄
    GetFirstElements lst
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
