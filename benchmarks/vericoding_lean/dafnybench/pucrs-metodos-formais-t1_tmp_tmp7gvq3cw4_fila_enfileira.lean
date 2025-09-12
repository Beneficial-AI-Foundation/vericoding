import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- enfileira satisfies the following properties. -/
def enfileira (e : Int) : Id Unit :=
  sorry

/-- Specification: enfileira satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem enfileira_spec (e : Int) :
    ⦃⌜True⌝⦄
    enfileira e
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
