

/-!
{
"name": "dafny-synthesis_task_id_581_SquarePyramidSurfaceArea",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_581_SquarePyramidSurfaceArea",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Calculates the surface area of a square pyramid given its base edge and height.

@param baseEdge The length of the base edge
@param height The height of the pyramid
@return The surface area of the square pyramid
-/
def SquarePyramidSurfaceArea (baseEdge : Int) (height : Int) : Int :=
sorry

/--
Specification for SquarePyramidSurfaceArea:
- Requires baseEdge > 0
- Requires height > 0
- Ensures the result equals baseEdge * baseEdge + 2 * baseEdge * height
-/
theorem SquarePyramidSurfaceArea_spec (baseEdge height : Int) :
baseEdge > 0 →
height > 0 →
SquarePyramidSurfaceArea baseEdge height = baseEdge * baseEdge + 2 * baseEdge * height :=
sorry
