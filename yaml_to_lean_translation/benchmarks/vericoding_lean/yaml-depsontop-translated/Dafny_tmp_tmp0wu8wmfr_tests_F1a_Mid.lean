```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "Dafny_tmp_tmp0wu8wmfr_tests_F1a_Mid",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Dafny_tmp_tmp0wu8wmfr_tests_F1a_Mid",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["Mid"]
}
-/

namespace DafnyBenchmarks

/--
Translates the Dafny Mid method which finds a middle point between two integers.
The method takes two integers p and q where p ≤ q and returns a middle point m
that satisfies specific constraints about its position between p and q.

@param p The lower bound integer
@param q The upper bound integer
@return m A middle point between p and q satisfying the specified constraints
-/
def Mid (p q : Int) : Int := sorry

/--
Specification for the Mid method ensuring:
1. The result m is between p and q inclusive
2. The distance from p to m is at most the distance from m to q
3. The difference between these distances is at most 1
-/
theorem Mid_spec (p q : Int) :
  p ≤ q →
  let m := Mid p q
  (p ≤ m ∧ m ≤ q) ∧
  (m - p ≤ q - m) ∧
  (0 ≤ (q - m) - (m - p) ∧ (q - m) - (m - p) ≤ 1) := sorry

end DafnyBenchmarks
```