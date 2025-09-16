

/-!
{
"name": "dafny-synthesis_task_id_171_PentagonPerimeter",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_171_PentagonPerimeter",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Calculates the perimeter of a pentagon given the side length.

@param side The length of one side of the pentagon
@return The perimeter of the pentagon

Requires:
- side > 0

Ensures:
- Result equals 5 * side
-/
def PentagonPerimeter (side : Int) : Int := sorry

/--
Specification for PentagonPerimeter function
-/
theorem PentagonPerimeter_spec (side : Int) :
side > 0 → PentagonPerimeter side = 5 * side := sorry
