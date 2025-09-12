```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_233_CylinderLateralSurfaceArea",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_233_CylinderLateralSurfaceArea", 
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["CylinderLateralSurfaceArea"]
}
-/

namespace DafnyBenchmarks

/--
Calculates the lateral surface area of a cylinder given its radius and height.
Requires positive radius and height.
Ensures the area is 2π * radius * height.
-/
def CylinderLateralSurfaceArea (radius : Real) (height : Real) : Real := sorry

/--
Specification for CylinderLateralSurfaceArea:
- Requires radius and height to be positive
- Ensures the returned area equals 2π * radius * height
-/
theorem CylinderLateralSurfaceArea_spec (radius height : Real) :
  radius > 0 ∧ height > 0 →
  CylinderLateralSurfaceArea radius height = 2 * (radius * height) * 3.14 := sorry

end DafnyBenchmarks
```