import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_441_CubeSurfaceArea",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_441_CubeSurfaceArea",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Calculates the surface area of a cube given its size.

@param size The length of a side of the cube
@return The total surface area of the cube

Translated from Dafny method:
dafny
method CubeSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 6 * size * size

-/
def CubeSurfaceArea (size : Int) : Int := sorry

/--
Specification for CubeSurfaceArea ensuring the result is correct.
-/
theorem CubeSurfaceArea_spec (size : Int) :
  size > 0 → CubeSurfaceArea size = 6 * size * size := sorry

end DafnyBenchmarks