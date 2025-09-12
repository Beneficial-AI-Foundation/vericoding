import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsDivisibleBy11 satisfies the following properties. -/
def IsDivisibleBy11 (n : Int) : Id Unit :=
  sorry

/-- Specification: IsDivisibleBy11 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsDivisibleBy11_spec (n : Int) :
    ⦃⌜True⌝⦄
    IsDivisibleBy11 n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
