

/-!
{
"name": "dafny-synthesis_task_id_430_ParabolaDirectrix",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_430_ParabolaDirectrix",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Calculates the directrix of a parabola given its parameters a, h, and k.
Input:
- a: Real number coefficient (must not be 0)
- h: Real number representing x-coordinate of vertex
- k: Real number representing y-coordinate of vertex
Output:
- directrix: Real number representing the directrix value
-/
def ParabolaDirectrix (a : Float) (h : Float) (k : Float) : Float :=
sorry

/--
Specification for ParabolaDirectrix:
- Requires a ≠ 0
- Ensures directrix = k - 1/(4*a)
-/
theorem ParabolaDirectrix_spec (a h k : Float) :
a ≠ 0 →
ParabolaDirectrix a h k = k - 1/(4*a) := sorry
