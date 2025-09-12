/-
  Port of vericoding_dafnybench_0753_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Empty  : PQueue :=
  sorry  -- TODO: implement function body

def Insert (pq : PQueue) (y : Int) : PQueue :=
  sorry  -- TODO: implement function body

function RemoveMin(pq: PQueue): (int, PQueue)
  var Node(x, left, right) := pq; (x, DeleteMin(pq))

def DeleteMin (pq : PQueue) : PQueue :=
  // Ex. 10.4: by the IsBalanced property, pq.left is always as large or one node larger // than pq.right. Thus pq.left.Leaf? → pq.right.leaf? if pq.right.Leaf? then pq.left else if pq.left.x ≤ pq.right.x then Node(pq.left.x, pq.right, DeleteMin(pq.left)) else Node(pq.right.x, ReplaceRoot(pq.right, pq.left.x), DeleteMin(pq.left))

def ReplaceRoot (pq : PQueue) (r : Int) : PQueue :=
  // left is empty or r is smaller than either sub-root if pq.left.Leaf? ∨ (r ≤ pq.left.x ∧ (pq.right.Leaf? ∨ r ≤ pq.right.x)) then // simply replace the root Node(r, pq.left, pq.right) // right is empty, left has one element else if pq.right.Leaf? then Node(pq.left.x, Node(r, Leaf, Leaf), Leaf) // both left/right are non-empty and `r` needs to be inserted deeper in the sub-trees else if pq.left.x < pq.right.x then // promote left root Node(pq.left.x, ReplaceRoot(pq.left, r), pq.right) else // promote right root Node(pq.right.x, pq.left, ReplaceRoot(pq.right, r))


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks