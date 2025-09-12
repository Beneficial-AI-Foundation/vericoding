```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-language-server_tmp_tmpkir0kenl_Test_VSComp2010_Problem1-SumMax_M",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-language-server_tmp_tmpkir0kenl_Test_VSComp2010_Problem1-SumMax_M", 
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["M"]
}
-/

namespace DafnyBenchmarks

/--
Method M computes the sum and max of an array of integers.
Translated from Dafny specification that requires:
- N is non-negative
- Array length equals N
- All array elements are non-negative
Ensures that sum ≤ N * max
-/
def M (N : Int) (a : Array Int) : Int × Int := sorry

/--
Specification for method M stating its preconditions and postcondition
-/
theorem M_spec (N : Int) (a : Array Int) :
  (N ≥ 0 ∧ a.size = N ∧ (∀ k, 0 ≤ k ∧ k < N → 0 ≤ a.get k)) →
  let (sum, max) := M N a
  sum ≤ N * max := sorry

end DafnyBenchmarks
```