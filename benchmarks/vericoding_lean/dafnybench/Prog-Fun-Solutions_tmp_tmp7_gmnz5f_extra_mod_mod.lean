import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- f satisfies the following properties. -/
def f (n : Nat) : Id Unit :=
  sorry

/-- Specification: f satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem f_spec (n : Nat) :
    ⦃⌜True⌝⦄
    f n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
