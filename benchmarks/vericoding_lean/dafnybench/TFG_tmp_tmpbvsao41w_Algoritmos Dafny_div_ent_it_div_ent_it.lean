import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- div_ent_it satisfies the following properties. -/
def div_ent_it (a : Int) : Id Unit :=
  sorry

/-- Specification: div_ent_it satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem div_ent_it_spec (a : Int) :
    ⦃⌜True⌝⦄
    div_ent_it a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
