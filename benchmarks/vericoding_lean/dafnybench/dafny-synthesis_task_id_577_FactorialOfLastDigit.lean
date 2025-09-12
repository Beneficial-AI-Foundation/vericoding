import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FactorialOfLastDigit satisfies the following properties. -/
def FactorialOfLastDigit (n : Int) : Id Unit :=
  sorry

/-- Specification: FactorialOfLastDigit satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FactorialOfLastDigit_spec (n : Int) :
    ⦃⌜True⌝⦄
    FactorialOfLastDigit n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
