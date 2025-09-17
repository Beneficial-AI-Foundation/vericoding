

/-!
{
"name": "Prog-Fun-Solutions_tmp_tmp7_gmnz5f_extra_mod2_mod2",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Prog-Fun-Solutions_tmp_tmp7_gmnz5f_extra_mod2_mod2",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Ghost function f2 that recursively computes a value based on input n.
For n = 0, returns 0
For n > 0, returns 5*f2(n/3) + n%4
-/
def f2 (n : Nat) : Nat :=
if n = 0 then 0
else 5 * f2 (n / 3) + n % 4

/--
Method mod2 that returns a value equal to f2(n)
-/
def mod2 (n : Nat) : Nat := sorry

/--
Specification for mod2 ensuring its result equals f2(n)
-/
theorem mod2_spec (n : Nat) : mod2 n = f2 n := sorry
