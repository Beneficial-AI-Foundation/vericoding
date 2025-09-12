```lean
import Std.Do.Triple
import Std.Tactic.Do
import Mathlib.Data.Int.Basic
import Mathlib.Data.Array.Basic

open Std.Do

/-!
{
  "name": "Clover_triple4_Triple",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: Clover_triple4_Triple",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["Triple"]
}
-/

namespace DafnyBenchmarks

/--
Translates the Dafny method Triple which returns triple the input value.
Original ensures clause: r == 3*x
-/
def Triple (x : Int) : Int := sorry

/--
Specification theorem for Triple method stating that the output is triple the input.
-/
theorem Triple_spec (x : Int) : Triple x = 3 * x := sorry

end DafnyBenchmarks
```