import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IndexWiseAddition satisfies the following properties. -/
def IndexWiseAddition (a : seq<seq<int>>) : Id Unit :=
  sorry

/-- Specification: IndexWiseAddition satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IndexWiseAddition_spec (a : seq<seq<int>>) :
    ⦃⌜True⌝⦄
    IndexWiseAddition a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
