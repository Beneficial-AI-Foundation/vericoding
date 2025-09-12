import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- LongestCommonPrefix satisfies the following properties. -/
def LongestCommonPrefix (str1 : seq<char>) : Id Unit :=
  sorry

/-- Specification: LongestCommonPrefix satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem LongestCommonPrefix_spec (str1 : seq<char>) :
    ⦃⌜True⌝⦄
    LongestCommonPrefix str1
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
