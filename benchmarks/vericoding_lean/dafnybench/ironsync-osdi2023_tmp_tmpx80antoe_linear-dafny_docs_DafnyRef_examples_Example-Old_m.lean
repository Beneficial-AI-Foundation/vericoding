import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- m satisfies the following properties. -/
def m (i : Int) : Id Unit :=
  sorry

/-- Specification: m satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem m_spec (i : Int) :
    ⦃⌜True⌝⦄
    m i
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
