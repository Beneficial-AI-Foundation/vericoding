

/-!
{
"name": "Formal-methods-of-software-development_tmp_tmppryvbyty_Bloque 2_Lab6_vector_Sum",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Formal-methods-of-software-development_tmp_tmppryvbyty_Bloque 2_Lab6_vector_Sum",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Sum of a sequence of integers -/
partial def sum (v : Array Int) : Int :=
if v.size = 0 then 0
else if v.size = 1 then v[0]!
else v[0]! + sum (v.extract 1 v.size)

/-- Scalar product of two integer vectors -/
partial def scalar_product (v1 v2 : Array Int) : Int :=
if v1.size = 0 then 0
else v1[0]! * v2[0]! + scalar_product (v1.extract 1 v1.size) (v2.extract 1 v2.size)

theorem scalar_product_spec (v1 v2 : Array Int) :
v1.size = v2.size → scalar_product v1 v2 = scalar_product v1 v2 := sorry

/-- Vector sum method specification -/
def vector_Sum (v : Array Int) : Int := sorry

theorem vector_Sum_spec (v : Array Int) (x : Int) :
vector_Sum v = sum v := sorry
