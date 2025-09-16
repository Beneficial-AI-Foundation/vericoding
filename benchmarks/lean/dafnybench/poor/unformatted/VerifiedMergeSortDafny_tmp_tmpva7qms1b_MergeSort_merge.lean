

/-!
{
"name": "VerifiedMergeSortDafny_tmp_tmpva7qms1b_MergeSort_merge",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: VerifiedMergeSortDafny_tmp_tmpva7qms1b_MergeSort_merge",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/

/-- Count occurrences of element x in array a -/
def count (a : Array Int) (x : Int) : Nat :=
a.foldl (fun acc y => if y = x then acc + 1 else acc) 0


/-- Predicate indicating if two sequences are merged into an array slice -/
def merged (a1 : Array Int) (a2 : Array Int) (b : Array Int) (start : Int) (end_ : Int) : Bool :=
end_ - start == a1.size + a2.size ∧
0 ≤ start ∧ start ≤ end_ ∧ end_ ≤ b.size ∧
-- Multiset equality: same count for each element in the slice
(∀ x : Int, count a1 x + count a2 x = count (b.extract start.toNat end_.toNat) x)

/-- Predicate indicating if an array slice is sorted -/
def sorted_slice (a : Array Int) (start : Int) (end_ : Int) : Prop :=
0 ≤ start ∧ start ≤ end_ ∧ end_ ≤ a.size ∧
∀ i j:Nat, start ≤ i ∧ i ≤ j ∧ j < end_ → a[i]! ≤ a[j]!

/-- Predicate indicating if a sequence is sorted -/
def sorted_seq (a : Array Int) : Prop :=
∀ i j:Nat, 0 ≤ i ∧ i ≤ j ∧ j < a.size → a[i]! ≤ a[j]!

/-- Predicate indicating if an array is sorted -/
def sorted (a : Array Int) : Prop :=
∀ i j:Nat, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!

/-- Merge two sorted sequences into an array -/
def merge (a1 : Array Int) (a2 : Array Int) (start : Int) (end_ : Int) (b : Array Int) : Array Int :=
sorry

/-- Specification for merge function -/
theorem merge_spec (a1 : Array Int) (a2 : Array Int) (start : Int) (end_ : Int) (b : Array Int) :
sorted_seq a1 ∧
sorted_seq a2 ∧
end_ - start == a1.size + a2.size ∧
0 ≤ start ∧ start < end_ ∧ end_ < a1.size ∧ end_ ≤ a2.size ∧ end_ < b.size ∧
end_ < a1.size ∧ end_ < a2.size ∧
b.size == a2.size + a1.size
→
sorted_slice (merge a1 a2 start end_ b) start end_ ∧
merged a1 a2 (merge a1 a2 start end_ b) start end_ := sorry
