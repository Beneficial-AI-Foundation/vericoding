/-
  Port of AssertivePrograming_tmp_tmpwf43uz0e_MergeSort_spec.dfy
  
  This specification describes the merge sort algorithm:
  - MergeSort: Recursively sorts an array by dividing it into two halves
  - Merge: Combines two sorted arrays into one sorted array
  
  The implementation should maintain the multiset of elements while sorting.
-/

namespace DafnyBenchmarks

/-- Predicate to check if an array is sorted -/
def Sorted (a : Array Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i ≤ j ∧ j < a.size → a[i]! ≤ a[j]!

/-- Merge two sorted arrays into one sorted array -/
def merge (c d : Array Int) : Array Int :=
  let rec loop (i j : Nat) (acc : Array Int) : Array Int :=
    if i ≥ c.size then
      acc ++ d.extract j d.size
    else if j ≥ d.size then
      acc ++ c.extract i c.size
    else if c[i]! ≤ d[j]! then
      loop (i + 1) j (acc.push c[i]!)
    else
      loop i (j + 1) (acc.push d[j]!)
  termination_by c.size + d.size - i - j
  loop 0 0 #[]

/-- Merge sort implementation -/
def mergeSort (a : Array Int) : Array Int :=
  if a.size ≤ 1 then a
  else
    let mid := a.size / 2
    let left := mergeSort (a.extract 0 mid)
    let right := mergeSort (a.extract mid a.size)
    merge left right
termination_by a.size

/-- Count occurrences of an element in an array -/
def count (a : Array Int) (x : Int) : Nat :=
  a.foldl (fun acc y => if y = x then acc + 1 else acc) 0

/-- Arrays have same elements (multiset equality) -/
def sameElements (a b : Array Int) : Prop :=
  a.size = b.size ∧ ∀ x, count a x = count b x

/-- Specification for mergeSort -/
theorem mergeSort_spec (a : Array Int) :
    let b := mergeSort a
    b.size = a.size ∧ 
    Sorted b ∧ 
    sameElements a b := by
  sorry

/-- Specification for merge -/
theorem merge_spec (c d : Array Int) 
    (h1 : Sorted c) 
    (h2 : Sorted d) :
    let b := merge c d
    Sorted b ∧ 
    b.size = c.size + d.size ∧
    ∀ x, count b x = count c x + count d x := by
  sorry

/-- Loop invariant for merge: subset preservation -/
def InvSubSet (b c d : Array Int) (i j : Nat) : Prop :=
  i ≤ c.size ∧ j ≤ d.size ∧ i + j ≤ b.size ∧
  ∀ x, count (b.extract 0 (i + j)) x = 
    count (c.extract 0 i) x + count (d.extract 0 j) x

/-- Loop invariant for merge: sortedness -/
def InvSorted (b c d : Array Int) (i j : Nat) : Prop :=
  i ≤ c.size ∧ j ≤ d.size ∧ i + j ≤ b.size ∧
  ((i + j > 0 ∧ i < c.size) → b[i + j - 1]! ≤ c[i]!) ∧
  ((i + j > 0 ∧ j < d.size) → b[i + j - 1]! ≤ d[j]!) ∧
  Sorted (b.extract 0 (i + j))

end DafnyBenchmarks