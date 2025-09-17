

/-!
{
"name": "Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_10_Hoangkim_ex10_hoangkim_strange",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_10_Hoangkim_ex10_hoangkim_strange",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Translation of method q from Dafny.
Original requires: y - x > 2
Original ensures: x < z*z < y
-/
def q (x : Nat) (y : Nat) : Nat :=
sorry

/--
Specification for method q
-/
theorem q_spec (x y : Nat) :
y - x > 2 → ∃ z, x < z*z ∧ z*z < y := sorry

/--
Translation of method strange from Dafny.
Original ensures: 1 == 2
-/
def strange : Unit :=
sorry

/--
Specification for method strange
-/
theorem strange_spec :
1 = 2 := sorry
