import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- AddTupleToList satisfies the following properties. -/
def AddTupleToList (l : seq<(int, int : α) : Id Unit :=
  sorry

/-- Specification: AddTupleToList satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem AddTupleToList_spec (l : seq<(int, int : α) :
    ⦃⌜True⌝⦄
    AddTupleToList l int
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
