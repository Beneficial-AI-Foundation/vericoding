

/-!
{
"name": "CVS-Projto1_tmp_tmpb1o0bu8z_proj1_proj1_queryFast",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: CVS-Projto1_tmp_tmpb1o0bu8z_proj1_proj1_queryFast",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Recursive sum function over array slice -/
partial def sum (a : Array Int) (i j : Int) : Int :=
if i = j then
0
else
a[(j-1).toNat]! + sum a i (j-1)

/-- Predicate checking if array c is prefix sum of array a -/
def is_prefix_sum_for (a c : Array Int) : Prop :=
a.size + 1 = c.size ∧
c[0]! = 0 ∧
∀ j, 1 ≤ j ∧ j ≤ a.size → c[j]! = sum a 0 j

/-- List datatype definition -/
inductive List (T : Type)
| Nil : List T
| Cons : T → List T → List T

/-- Check if element exists in list -/
def mem {T : Type} [BEq T] (x : T) (l : List T) : Bool :=
match l with
| List.Nil => false
| List.Cons y r => if x == y then true else mem x r

/-- Convert array to list -/
def from_array {T : Type} (a : Array T) : List T :=
sorry



/-- Fast query implementation -/
def queryFast (a c : Array Int) (i j : Int) : Int :=
sorry

/-- Fast query method specification -/
theorem queryFast_spec (a c : Array Int) (i j : Int) :
is_prefix_sum_for a c ∧
0 ≤ i ∧ i ≤ j ∧ j ≤ a.size ∧ a.size < c.size →
queryFast a c i j = sum a i j := sorry
