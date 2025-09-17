

/-!
{
"name": "dafny-synthesis_task_id_14_TriangularPrismVolume",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_14_TriangularPrismVolume",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Calculates the volume of a triangular prism given base, height and length.

@param base The base length of the triangular face
@param height The height of the triangular face
@param length The length of the prism
@return The volume of the triangular prism
-/
def TriangularPrismVolume (base : Int) (height : Int) (length : Int) : Int := sorry

/--
Specification for TriangularPrismVolume:
- Requires base > 0
- Requires height > 0
- Requires length > 0
- Ensures volume = (base * height * length) / 2
-/
theorem TriangularPrismVolume_spec (base height length : Int) :
base > 0 →
height > 0 →
length > 0 →
TriangularPrismVolume base height length = (base * height * length) / 2 := sorry
