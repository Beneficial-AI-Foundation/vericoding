

/-!
{
"name": "dafny-synthesis_task_id_626_AreaOfLargestTriangleInSemicircle",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_626_AreaOfLargestTriangleInSemicircle",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Calculates the area of the largest triangle that can be inscribed in a semicircle.

@param radius The radius of the semicircle (must be positive)
@return The area of the largest inscribed triangle
-/
def AreaOfLargestTriangleInSemicircle (radius : Int) : Int := sorry

/--
Specification for AreaOfLargestTriangleInSemicircle:
- Requires radius to be positive
- Ensures the returned area equals radius squared
-/
theorem AreaOfLargestTriangleInSemicircle_spec (radius : Int) :
radius > 0 →
AreaOfLargestTriangleInSemicircle radius = radius * radius := sorry
