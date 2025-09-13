import Std

open Std.Do

/-!
{
  "name": "Dafny-Practice_tmp_tmphnmt4ovh_BST_InsertBST",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Dafny-Practice_tmp_tmphnmt4ovh_BST_InsertBST",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/-- Binary tree datatype -/
inductive Tree where
  | Empty : Tree
  | Node : Int → Tree → Tree → Tree
  deriving Repr



/-- Convert sequence to set -/
def NumbersInSequence (q : Array Int) : List Int :=
  q.toList

/-- Get inorder traversal of tree -/
def Inorder (t : Tree) : Array Int :=
  match t with
  | Tree.Empty => #[]
  | Tree.Node n t1 t2 => (Inorder t1).append (#[n]) ++ (Inorder t2)

/-- Get set of numbers in a tree -/
def NumbersInTree (t : Tree) : List Int :=
  NumbersInSequence (Inorder t)
/-- Check if sequence is ascending -/
def Ascending (q : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < q.size → q[i]! < q[j]!

/-- Check if tree is a binary search tree -/
def BST (t : Tree) : Prop :=
  Ascending (Inorder t)



/-- Check if sequence has no duplicates -/
def NoDuplicates (q : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < q.size → q[i]! ≠ q[j]!

/-- Insert value into BST maintaining BST property -/
def InsertBST (t0 : Tree) (x : Int) : Tree := sorry

/-- Specification for InsertBST -/
theorem InsertBST_spec (t0 : Tree) (x : Int) :
  BST t0 ∧ x ∉ NumbersInTree t0 →
  let t := InsertBST t0 x
  BST t ∧ NumbersInTree t = NumbersInTree t0 ++ [x] := sorry

end DafnyBenchmarks
