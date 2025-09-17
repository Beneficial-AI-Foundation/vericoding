

/-!
{
"name": "dafny-synthesis_task_id_574_CylinderSurfaceArea",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_574_CylinderSurfaceArea",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Calculates the surface area of a cylinder given radius and height.
Requires positive radius and height.
Returns the surface area using the formula: 2πr(r + h)
-/
def CylinderSurfaceArea (radius : Float) (height : Float) : Float := sorry

/--
Specification for CylinderSurfaceArea:
- Requires radius and height to be positive
- Ensures the result is 2πr(r + h)
-/
theorem CylinderSurfaceArea_spec (radius height : Float) :
radius > 0 ∧ height > 0 →
CylinderSurfaceArea radius height = 2 * 3.14159265358979323846 * radius * (radius + height) := sorry
