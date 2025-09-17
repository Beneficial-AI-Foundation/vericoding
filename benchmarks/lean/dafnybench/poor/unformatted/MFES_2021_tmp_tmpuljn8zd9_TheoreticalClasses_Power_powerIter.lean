

/-!
{
"name": "MFES_2021_tmp_tmpuljn8zd9_TheoreticalClasses_Power_powerIter",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: MFES_2021_tmp_tmpuljn8zd9_TheoreticalClasses_Power_powerIter",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Initial specification/definition of x^n, recursive, functional style,
with time and space complexity O(n).
-/
def power (x : Float) (n : Nat) : Float :=
match n with
| 0 => 1.0
| n + 1 => x * power x n

/--
Iterative version, imperative, with time complexity O(n) and space complexity O(1).
-/
def powerIter (x : Float) (n : Nat) : Float := sorry

/--
Specification for powerIter ensuring it matches the recursive power function
-/
theorem powerIter_spec (x : Float) (n : Nat) :
powerIter x n = power x n := sorry
