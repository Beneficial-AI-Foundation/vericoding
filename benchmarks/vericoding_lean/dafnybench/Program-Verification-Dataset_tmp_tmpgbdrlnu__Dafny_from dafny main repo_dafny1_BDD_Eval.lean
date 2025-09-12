import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Eval satisfies the following properties. -/
def Eval (s : seq<bool>) : Id Unit :=
  sorry

/-- Specification: Eval satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Eval_spec (s : seq<bool>) :
    ⦃⌜True⌝⦄
    Eval s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
