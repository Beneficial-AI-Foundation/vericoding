-- <vc-preamble>
inductive Tree where
| Empty : Tree
| Node : Int → Tree → Tree → Tree
deriving Repr
def NumbersInSequence (q : Array Int) : List Int :=
q.toList
def Inorder (t : Tree) : Array Int :=
match t with
| Tree.Empty => #[]
| Tree.Node n t1 t2 => (Inorder t1).append (#[n]) ++ (Inorder t2)
def NumbersInTree (t : Tree) : List Int :=
NumbersInSequence (Inorder t)
def Ascending (q : Array Int) : Prop :=
∀ i j : Nat, i < j → j < q.size → q[i]! < q[j]!
def BST (t : Tree) : Prop :=
Ascending (Inorder t)
def NoDuplicates (q : Array Int) : Prop :=
∀ i j : Nat, i < j → j < q.size → q[i]! ≠ q[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def InsertBST (t0 : Tree) (x : Int) : Tree :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem InsertBST_spec (t0 : Tree) (x : Int) :
BST t0 ∧ x ∉ NumbersInTree t0 →
let t := InsertBST t0 x
BST t ∧ NumbersInTree t = NumbersInTree t0 ++ [x] :=
sorry
-- </vc-theorems>