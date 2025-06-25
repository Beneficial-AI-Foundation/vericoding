pub fn InsertBST(t0: Tree, x: int) -> (t: Tree)
    requires(BST(t0) && x !in NumbersInTree(t0))
    ensures(BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x})
{
}

pub fn lemma_all_small(q: seq<int>, i: int)
    requires(forall|k| k in NumbersInSequence(q) ==> k < i)
    requires(forall|k| 0 <= k < |q| ==> q[k] in NumbersInSequence(q))
    ensures(forall|j| 0 <= j < |q| ==> q[j] < i)
{
}

pub fn lemma_all_big(q: seq<int>, i: int)
    requires(forall|k| k in NumbersInSequence(q) ==> k > i)
    requires(forall|k| 0 <= k < |q| ==> q[k] in NumbersInSequence(q))
    ensures(forall|j| 0 <= j < |q| ==> q[j] > i)
{
}