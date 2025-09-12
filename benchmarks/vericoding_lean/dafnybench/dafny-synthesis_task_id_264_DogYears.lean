import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- DogYears satisfies the following properties. -/
def DogYears (humanYears : Int) : Id Unit :=
  sorry

/-- Specification: DogYears satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem DogYears_spec (humanYears : Int) :
    ⦃⌜True⌝⦄
    DogYears humanYears
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
