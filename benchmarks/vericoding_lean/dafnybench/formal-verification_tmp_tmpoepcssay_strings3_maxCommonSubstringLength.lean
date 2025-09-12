import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- haveCommonKSubstring satisfies the following properties. -/
def haveCommonKSubstring (k : Nat) : Id Unit :=
  sorry

/-- Specification: haveCommonKSubstring satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem haveCommonKSubstring_spec (k : Nat) :
    ⦃⌜True⌝⦄
    haveCommonKSubstring k
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
