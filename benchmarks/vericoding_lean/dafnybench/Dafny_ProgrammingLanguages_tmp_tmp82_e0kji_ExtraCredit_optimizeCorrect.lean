import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- eval satisfies the following properties. -/
def eval (e : Exp) : Id Unit :=
  sorry

/-- Specification: eval satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem eval_spec (e : Exp) :
    ⦃⌜True⌝⦄
    eval e
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
