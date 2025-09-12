import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsPalindrome satisfies the following properties. -/
def IsPalindrome (x : seq<char>) : Id Unit :=
  sorry

/-- Specification: IsPalindrome satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsPalindrome_spec (x : seq<char>) :
    ⦃⌜True⌝⦄
    IsPalindrome x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
