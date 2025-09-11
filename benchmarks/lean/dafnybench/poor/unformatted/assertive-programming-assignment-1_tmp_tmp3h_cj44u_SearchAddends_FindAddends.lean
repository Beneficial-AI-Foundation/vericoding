

/-!
{
"name": "assertive-programming-assignment-1_tmp_tmp3h_cj44u_SearchAddends_FindAddends",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: assertive-programming-assignment-1_tmp_tmp3h_cj44u_SearchAddends_FindAddends",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Predicate indicating if an array is sorted in ascending order -/
def Sorted (q : Array Int) : Prop :=
∀ i j, 0 ≤ i → i ≤ j → j < q.size → q[i]! ≤ q[j]!

/-- Predicate indicating if there exist two indices whose elements sum to x -/
def HasAddends (q : Array Int) (x : Int) : Prop :=
∃ i j, 0 ≤ i ∧ i < j ∧ j < q.size ∧ q[i]! + q[j]! = x

/-- Predicate indicating if an index is valid for an array -/
def IsValidIndex {T : Type} (q : Array T) (i : Nat) : Prop :=
0 ≤ i ∧ i < q.size

/-- Predicate indicating if two indices are ordered within array bounds -/
def AreOrderedIndices {T : Type} (q : Array T) (i j : Nat) : Prop :=
0 ≤ i ∧ i < j ∧ j < q.size

/-- Predicate indicating if two indices contain elements that sum to x -/
def AreAddendsIndices (q : Array Int) (x : Int) (i j : Nat) : Prop :=
IsValidIndex q i ∧ IsValidIndex q j → q[i]! + q[j]! = x

/-- Predicate indicating if a subarray contains elements that sum to x -/
def HasAddendsInIndicesRange (q : Array Int) (x : Int) (i j : Nat) : Prop :=
AreOrderedIndices q i j → HasAddends (q.extract i (j + 1)) x

/-- Loop invariant predicate -/
def LoopInv (q : Array Int) (x : Int) (i j : Nat) (sum : Int) : Prop :=
AreOrderedIndices q i j ∧
HasAddendsInIndicesRange q x i j ∧
AreAddendsIndices q sum i j

/-- Main FindAddends method specification -/
theorem FindAddends_spec (q : Array Int) (x : Int) :
Sorted q → HasAddends q x →
∃ i j, i < j ∧ j < q.size ∧ q[i]! + q[j]! = x := sorry

/-- FindAddends implementation -/
def FindAddends (q : Array Int) (x : Int) : Nat × Nat := sorry