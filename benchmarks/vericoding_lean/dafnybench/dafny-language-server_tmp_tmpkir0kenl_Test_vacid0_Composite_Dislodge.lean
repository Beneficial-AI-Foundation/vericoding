import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Acyclic satisfies the following properties. -/
def Acyclic (S : set<Composite>) : Id Unit :=
  sorry

/-- Specification: Acyclic satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Acyclic_spec (S : set<Composite>) :
    ⦃⌜True⌝⦄
    Acyclic S
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
