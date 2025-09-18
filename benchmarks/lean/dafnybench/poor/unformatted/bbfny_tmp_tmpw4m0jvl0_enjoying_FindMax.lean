


/-!
{
"name": "bbfny_tmp_tmpw4m0jvl0_enjoying_FindMax",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: bbfny_tmp_tmpw4m0jvl0_enjoying_FindMax",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Translation of Dafny max function -/
def max (a b : Int) : Int :=
if a > b then a else b

/-- Translation of Dafny Testing method -/
def Testing : Unit := sorry

/-- Translation of Dafny abs function -/
def abs (x : Int) : Int :=
if x < 0 then -x else x

/-- Translation of Dafny fib function -/
def fib (n : Nat) : Nat :=
if n = 0 then 0
else if n = 1 then 1
else fib (n - 1) + fib (n - 2)

/-- Translation of Dafny sorted predicate -/
def sorted (a : Array Int) : Prop :=
∀ j k, 0 ≤ j → j < k → k < a.size → a[j]! < a[k]!

/-- Translation of FindMax method specification -/
def FindMax (a : Array Int) : Int := sorry

/-- Specification for FindMax -/
theorem FindMax_spec (a : Array Int) (i : Int) :
a.size ≥ 1 →
(0 ≤ i ∧ i < a.size) ∧
(∀ k, 0 ≤ k ∧ k < a.size → a[k]! ≤ a[i.toNat]!) := sorry
