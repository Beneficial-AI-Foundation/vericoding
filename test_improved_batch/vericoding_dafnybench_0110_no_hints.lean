/-
  Port of vericoding_dafnybench_0110_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def NumbersInTree (t : Tree) : set :=
  NumbersInSequence(Inorder(t))

def NumbersInSequence (q : seq<int>) : set :=
  set x | x in q

def Inorder (t : Tree) : seq :=
  match t { case Empty => [] case Node(n',nt1,nt2) => Inorder(nt1)+[n']+Inorder(nt2) }


  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def BuildBST (q : seq<int>) : Tree :=
  sorry  -- TODO: implement function body

theorem BuildBST_spec (q : seq<int>) (t : Tree) :=
  (h_0 : NoDuplicates(q))
  : BST(t) ∧ NumbersInTree(t) == NumbersInSequence(q)
  := by
  sorry  -- TODO: implement proof

def InsertBST (t0 : Tree) (x : Int) : Tree :=
  sorry  -- TODO: implement function body

theorem InsertBST_spec (t0 : Tree) (x : Int) (t : Tree) :=
  (h_0 : BST(t0) ∧ x !in NumbersInTree(t0))
  : BST(t) ∧ NumbersInTree(t) == NumbersInTree(t0)+{x}
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks