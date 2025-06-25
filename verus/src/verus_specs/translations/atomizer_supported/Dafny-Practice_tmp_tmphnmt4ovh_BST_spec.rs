// ATOM 
pub enum Tree {
    Empty,
    Node(int, Box<Tree>, Box<Tree>)
}

// SPEC 
pub fn Main() {
}

// SPEC 
pub fn PrintTreeNumbersInorder(t: Tree) {
}

// ATOM 
pub spec fn NumbersInTree(t: Tree) -> Set<int> {
    NumbersInSequence(Inorder(t))
}

// ATOM 
pub spec fn NumbersInSequence(q: Seq<int>) -> Set<int> {
    Set::new(|x: int| q.contains(x))
}

// ATOM 
pub spec fn BST(t: Tree) -> bool {
    Ascending(Inorder(t))
}

// ATOM 
pub spec fn Inorder(t: Tree) -> Seq<int> {
    match t {
        Tree::Empty => seq![],
        Tree::Node(n_, nt1, nt2) => Inorder(*nt1) + seq![n_] + Inorder(*nt2)
    }
}

// ATOM 
pub spec fn Ascending(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] < q[j]
}

// ATOM 
pub spec fn NoDuplicates(q: Seq<int>) -> bool { 
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] != q[j] 
}

// SPEC 
pub fn BuildBST(q: Seq<int>) -> (t: Tree)
    requires(NoDuplicates(q))
    ensures(BST(t) && NumbersInTree(t) == NumbersInSequence(q))
{
}

// SPEC 
pub fn InsertBST(t0: Tree, x: int) -> (t: Tree)
    requires(BST(t0) && !NumbersInTree(t0).contains(x))
    ensures(BST(t) && NumbersInTree(t) == NumbersInTree(t0).insert(x))
{
}

// ATOM 
pub proof fn LemmaBinarySearchSubtree(n: int, left: Tree, right: Tree)
    requires(BST(Tree::Node(n, Box::new(left), Box::new(right))))
    ensures(BST(left) && BST(right))
{
}

// ATOM 
pub proof fn LemmaAscendingSubsequence(q1: Seq<int>, q2: Seq<int>, i: nat)
    requires(i <= q1.len() - q2.len() && q2 == q1.subrange(i as int, i + q2.len()))
    requires(Ascending(q1))
    ensures(Ascending(q2))
{
}

pub proof fn lemma_all_small(q: Seq<int>, i: int)
    requires(forall|k: int| NumbersInSequence(q).contains(k) ==> k < i)
    requires(forall|k: int| 0 <= k < q.len() ==> NumbersInSequence(q).contains(q[k]))
    ensures(forall|j: int| 0 <= j < q.len() ==> q[j] < i)
{
}

pub proof fn lemma_all_big(q: Seq<int>, i: int)
    requires(forall|k: int| NumbersInSequence(q).contains(k) ==> k > i)
    requires(forall|k: int| 0 <= k < q.len() ==> NumbersInSequence(q).contains(q[k]))
    ensures(forall|j: int| 0 <= j < q.len() ==> q[j] > i)
{
}