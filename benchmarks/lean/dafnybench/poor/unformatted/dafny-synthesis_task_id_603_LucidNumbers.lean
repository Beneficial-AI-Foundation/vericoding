

/-!
{
"name": "dafny-synthesis_task_id_603_LucidNumbers",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_603_LucidNumbers",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Translates the Dafny LucidNumbers method which returns a sequence of numbers that are:
- Divisible by 3
- Less than or equal to input n
- In strictly increasing order
-/
def LucidNumbers (n : Int) : Array Int := sorry

/--
Main specification theorem for LucidNumbers capturing the three key properties:
1. All elements are divisible by 3
2. All elements are ≤ n
3. Elements are in strictly increasing order
-/
theorem LucidNumbers_spec (n : Int) :
n ≥ 0 →
let result := LucidNumbers n
(∀ i, 0 ≤ i ∧ i < result.size → (result[i]!) % 3 = 0) ∧
(∀ i, 0 ≤ i ∧ i < result.size → result[i]! ≤ n) ∧
(∀ i j, 0 ≤ i ∧ i < j ∧ j < result.size → result[i]! < result[j]!) := sorry
