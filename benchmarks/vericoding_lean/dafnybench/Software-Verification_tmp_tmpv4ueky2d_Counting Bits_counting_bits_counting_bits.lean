import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- counting_bits satisfies the following properties. -/
def counting_bits (n : Int) : Id Unit :=
  sorry

/-- Specification: counting_bits satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem counting_bits_spec (n : Int) :
    ⦃⌜True⌝⦄
    counting_bits n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
