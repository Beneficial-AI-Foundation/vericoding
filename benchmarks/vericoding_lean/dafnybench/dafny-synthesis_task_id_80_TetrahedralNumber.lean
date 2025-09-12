import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- TetrahedralNumber satisfies the following properties. -/
def TetrahedralNumber (n : Int) : Id Unit :=
  sorry

/-- Specification: TetrahedralNumber satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem TetrahedralNumber_spec (n : Int) :
    ⦃⌜True⌝⦄
    TetrahedralNumber n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
