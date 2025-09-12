import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsPrime satisfies the following properties. -/
def IsPrime (n : Int) : Id Unit :=
  sorry

/-- Specification: IsPrime satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsPrime_spec (n : Int) :
    ⦃⌜True⌝⦄
    IsPrime n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
