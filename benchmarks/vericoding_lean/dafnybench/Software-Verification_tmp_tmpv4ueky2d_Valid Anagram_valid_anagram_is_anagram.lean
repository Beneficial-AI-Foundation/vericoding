import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- is_anagram satisfies the following properties. -/
def is_anagram (s : String) : Id Unit :=
  sorry

/-- Specification: is_anagram satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem is_anagram_spec (s : String) :
    ⦃⌜True⌝⦄
    is_anagram s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
