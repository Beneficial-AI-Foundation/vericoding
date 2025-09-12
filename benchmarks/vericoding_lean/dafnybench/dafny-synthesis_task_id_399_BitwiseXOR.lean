import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- BitwiseXOR satisfies the following properties. -/
def BitwiseXOR (a : seq<bv32>) : Id Unit :=
  sorry

/-- Specification: BitwiseXOR satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem BitwiseXOR_spec (a : seq<bv32>) :
    ⦃⌜True⌝⦄
    BitwiseXOR a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
