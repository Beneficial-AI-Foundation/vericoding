import Std

open Std.Do

/-!
{
  "name": "Clover_multi_return_MultipleReturns",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Clover_multi_return_MultipleReturns",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Translates the Dafny method MultipleReturns which returns two values:
more = x + y and less = x - y
-/
def MultipleReturns (x y : Int) : Int × Int := sorry

/--
Specification for MultipleReturns ensuring:
1. The first return value equals x + y
2. The second return value equals x - y
-/
theorem MultipleReturns_spec (x y : Int) :
  let (more, less) := MultipleReturns x y
  more = x + y ∧ less = x - y := sorry

end DafnyBenchmarks
