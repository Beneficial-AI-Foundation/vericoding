

/-!
{
"name": "BPTree-verif_tmp_tmpq1z6xm1d_Utils_InsertIntoSorted",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: BPTree-verif_tmp_tmpq1z6xm1d_Utils_InsertIntoSorted",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Translates Dafny SetLessThan function -/
def SetLessThan (numbers : List Int) (threshold : Int) : List Int :=
numbers.filter (λ x => x < threshold)

/-- Translates Dafny seqSet function -/
def seqSet (nums : Array Int) (index : Nat) : List Int :=
sorry

/-- Translates Dafny SortedSeq predicate -/
def SortedSeq (a : Array Int) : Prop :=
∀ i j, 0 ≤ i → i < j → j < a.size → a[i]! < a[j]!

/-- Translates Dafny sorted predicate -/
def sorted (a : Array Int) : Prop :=
∀ i j, 0 ≤ i → i < j → j < a.size → a[i]! < a[j]!

/-- Translates Dafny distinct predicate -/
def distinct (a : Array Int) : Prop :=
∀ i j, 0 ≤ i → i < a.size → 0 ≤ j → j < a.size → i ≠ j → a[i]! ≠ a[j]!

/-- Translates Dafny sorted_eq predicate -/
def sorted_eq (a : Array Int) : Prop :=
∀ i j, 0 ≤ i → i < j → j < a.size → a[i]! ≤ a[j]!

/-- Translates Dafny lessThan predicate -/
def lessThan (a : Array Int) (key : Int) : Prop :=
∀ i, 0 ≤ i → i < a.size → a[i]! < key

/-- Translates Dafny greaterThan predicate -/
def greaterThan (a : Array Int) (key : Int) : Prop :=
∀ i, 0 ≤ i → i < a.size → a[i]! > key

/-- Translates Dafny greaterEqualThan predicate -/
def greaterEqualThan (a : Array Int) (key : Int) : Prop :=
∀ i, 0 ≤ i → i < a.size → a[i]! ≥ key

/-- Translates Dafny GetInsertIndex method -/
def GetInsertIndex (a : Array Int) (limit : Int) (x : Int) : Int :=
sorry

/-- Specification for GetInsertIndex -/
theorem GetInsertIndex_spec (a : Array Int) (limit : Int) (x : Int) :
(∀ i, 0 ≤ i → i < a.size → a[i]! ≠ x) →
0 ≤ limit → limit ≤ a.size →
SortedSeq a →
let idx := GetInsertIndex a limit x
0 ≤ idx ∧ idx ≤ limit ∧
SortedSeq a ∧
(idx > 0 → a[(idx - 1).toNat]! < x) ∧
(idx < limit → x < a[(idx).toNat]!) := sorry

/-- Translates Dafny InsertIntoSorted method -/
def InsertIntoSorted (a : Array Int) (limit : Int) (key : Int) : Array Int :=
sorry

/-- Specification for InsertIntoSorted -/
theorem InsertIntoSorted_spec (a : Array Int) (limit : Int) (key : Int) :
key > 0 →
(∀ i, 0 ≤ i → i < a.size → a[i]! ≠ key) →
0 ≤ limit → limit < a.size →
(∀ i, 0 ≤ i → i < limit → a[i.toNat]! > 0) →
(∀ i, limit ≤ i → i < a.size → a[i.toNat]! = 0) →
sorted a →
let b := InsertIntoSorted a limit key
b.size = a.size ∧
sorted b ∧
(∀ i, limit + 1 ≤ i → i < b.size → b[i.toNat]! = 0) ∧
(∀ i, 0 ≤ i → i < limit → ∃ j, 0 ≤ j → j < b.size → b[j]! = a[i.toNat]!) ∧
(∀ i, 0 ≤ i → i < limit + 1 → b[i.toNat]! > 0) := sorry