import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- isPalindrome satisfies the following properties. -/
def isPalindrome (s : array<char>) : Id Unit :=
  sorry

/-- Specification: isPalindrome satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem isPalindrome_spec (s : array<char>) :
    ⦃⌜True⌝⦄
    isPalindrome s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
