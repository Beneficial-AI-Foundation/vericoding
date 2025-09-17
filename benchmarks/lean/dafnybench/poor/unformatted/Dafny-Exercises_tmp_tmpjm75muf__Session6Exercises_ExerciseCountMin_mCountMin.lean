

/-!
{
"name": "Dafny-Exercises_tmp_tmpjm75muf__Session6Exercises_ExerciseCountMin_mCountMin",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Dafny-Exercises_tmp_tmpjm75muf__Session6Exercises_ExerciseCountMin_mCountMin",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Finds minimum value in array up to index i -/
partial def min (v : Array Int) (i : Nat) : Int :=
if i = 1 then v[0]!
else if v[i-1]! ≤ min v (i-1) then v[i-1]!
else min v (i-1)

/-- Specification for min function -/
theorem min_spec (v : Array Int) (i : Nat) :
1 ≤ i ∧ i ≤ v.size →
∀ k, 0 ≤ k ∧ k < i → v[k]! ≥ min v i := sorry

/-- Counts occurrences of x in array up to index i -/
partial def countMin (v : Array Int) (x : Int) (i : Nat) : Int :=
if i = 0 then 0
else if v[i-1]! = x then 1 + countMin v x (i-1)
else countMin v x (i-1)

/-- Specification for countMin function -/
theorem countMin_spec (v : Array Int) (x : Int) (i : Nat) :
0 ≤ i ∧ i ≤ v.size →
countMin v x i = 0 := sorry

/-- Main method that counts occurrences of minimum value -/
def mCountMin (v : Array Int) : Int := sorry

/-- Specification for mCountMin method -/
theorem mCountMin_spec (v : Array Int) :
v.size > 0 →
mCountMin v = countMin v (min v v.size) v.size := sorry
