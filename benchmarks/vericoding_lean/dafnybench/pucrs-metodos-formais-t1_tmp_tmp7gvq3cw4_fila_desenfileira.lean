import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- desenfileira satisfies the following properties. -/
def desenfileira (e : Int) : Id Unit :=
  sorry

/-- Specification: desenfileira satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem desenfileira_spec (e : Int) :
    ⦃⌜True⌝⦄
    desenfileira e
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
