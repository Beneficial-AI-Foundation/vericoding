//ATOM Tree
datatype Tree = Empty | Node(data: int, left: Tree, right: Tree)

//ATOM Main
method Main()
{
    var t := Node(5, Node(3, Empty, Empty), Node(7, Empty, Empty));
    PrintTreeNumbersInorder(t);
}

//IMPL PrintTreeNumbersInorder
method PrintTreeNumbersInorder(t: Tree)
    /* code modified by LLM (iteration 3): moved decreases clause from method body to method signature */
    decreases t
{
    match t
    {
        case Empty => 
        case Node(data, left, right) =>
            PrintTreeNumbersInorder(left);
            print data, " ";
            PrintTreeNumbersInorder(right);
    }
}

//ATOM NumbersInTree
function NumbersInTree(t: Tree): set<int>
{
    match t
    case Empty => {}
    case Node(data, left, right) => {data} + NumbersInTree(left) + NumbersInTree(right)
}

//ATOM NumbersInSequence
function NumbersInSequence(s: seq<int>): set<int>
{
    set i | 0 <= i < |s| :: s[i]
}

//ATOM BST
predicate BST(t: Tree)
{
    match t
    case Empty => true
    case Node(data, left, right) =>
        BST(left) && BST(right) &&
        (forall x :: x in NumbersInTree(left) ==> x < data) &&
        (forall x :: x in NumbersInTree(right) ==> x > data)
}

//ATOM Inorder
function Inorder(t: Tree): seq<int>
{
    match t
    case Empty => []
    case Node(data, left, right) => Inorder(left) + [data] + Inorder(right)
}

//ATOM Ascending
predicate Ascending(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

//ATOM NoDuplicates
predicate NoDuplicates(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

//ATOM BuildBST
method BuildBST(s: seq<int>) returns (t: Tree)
    requires NoDuplicates(s)
    ensures BST(t)
    ensures NumbersInTree(t) == NumbersInSequence(s)
{
    t := Empty;
    for i := 0 to |s|
        invariant BST(t)
        invariant NumbersInTree(t) == NumbersInSequence(s[..i])
    {
        t := InsertBST(t, s[i]);
    }
}

//ATOM InsertBST
method InsertBST(t0: Tree, x: int) returns (t: Tree)
    requires BST(t0)
    requires x !in NumbersInTree(t0)
    ensures BST(t)
    ensures NumbersInTree(t) == NumbersInTree(t0) + {x}
{
    match t0 
    {
        case Empty => t := Node(x, Empty, Empty);

        case Node(i, left, right) => 
        {
            var tmp: Tree := Empty;
            if x < i
            {
                LemmaBinarySearchSubtree(i, left, right);
                tmp := InsertBST(left, x);
                t := Node(i, tmp, right);
                ghost var right_nums := Inorder(right);
                ghost var left_nums := Inorder(left);
                ghost var all_nums := Inorder(t0);
                ghost var new_all_nums := Inorder(t);
                ghost var new_left_nums := Inorder(tmp);
                
                lemma_all_small(new_left_nums, i);
            }
            else
            {
                LemmaBinarySearchSubtree(i, left, right);
                tmp := InsertBST(right, x);
                t := Node(i, left, tmp);

                ghost var right_nums := Inorder(right);
                ghost var left_nums := Inorder(left);
                ghost var all_nums := Inorder(t0);
                ghost var new_all_nums := Inorder(t);
                ghost var new_right_nums := Inorder(tmp);
                
                lemma_all_big(new_right_nums, i);
            }
        }
    }
}

//ATOM LemmaBinarySearchSubtree
lemma LemmaBinarySearchSubtree(data: int, left: Tree, right: Tree)
    requires BST(Node(data, left, right))
    ensures BST(left) && BST(right)
    ensures forall x :: x in NumbersInTree(left) ==> x < data
    ensures forall x :: x in NumbersInTree(right) ==> x > data
{
}

//ATOM LemmaAscendingSubsequence
lemma LemmaAscendingSubsequence(s: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |s|
    requires Ascending(s)
    ensures Ascending(s[i..j])
{
}

//ATOM lemma_all_small
lemma lemma_all_small(q: seq<int>, i: int)
    requires forall k :: k in NumbersInSequence(q) ==> k < i
    requires forall k :: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
    ensures forall j :: 0 <= j < |q| ==> q[j] < i
{
}

//ATOM lemma_all_big
lemma lemma_all_big(q: seq<int>, i: int)
    requires forall k :: k in NumbersInSequence(q) ==> k > i
    requires forall k :: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
    ensures forall j :: 0 <= j < |q| ==> q[j] > i
{
}