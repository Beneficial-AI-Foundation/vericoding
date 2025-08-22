//ATOM Tree
datatype Tree = Empty | Node(n: int, left: Tree, right: Tree)

//ATOM Main
method Main() {
    var t := BuildBST([5, 3, 7, 1, 9]);
    PrintTreeNumbersInorder(t);
}

//ATOM PrintTreeNumbersInorder
method PrintTreeNumbersInorder(t: Tree) {
    var inorder := Inorder(t);
    print "Tree numbers in order: ";
    var i := 0;
    while i < |inorder|
    {
        print inorder[i];
        if i < |inorder| - 1 {
            print ", ";
        }
        i := i + 1;
    }
    print "\n";
}

//ATOM NumbersInTree
function NumbersInTree(t: Tree): set<int>
{
	NumbersInSequence(Inorder(t))
}

//ATOM NumbersInSequence
function NumbersInSequence(q: seq<int>): set<int>
{
	set x | x in q
}

//ATOM BST
predicate BST(t: Tree)
{
	Ascending(Inorder(t))
}

//ATOM Inorder
function Inorder(t: Tree): seq<int>
{
	match t {
		case Empty => []
		case Node(n',nt1,nt2) => Inorder(nt1)+[n']+Inorder(nt2)
	}
}

//ATOM Ascending
predicate Ascending(q: seq<int>)
{
	forall i,j :: 0 <= i < j < |q| ==> q[i] < q[j]
}

//ATOM NoDuplicates
predicate NoDuplicates(q: seq<int>)
{
    forall i, j :: 0 <= i < j < |q| ==> q[i] != q[j]
}

//ATOM BuildBST
method BuildBST(nums: seq<int>) returns (t: Tree)
    requires NoDuplicates(nums)
    ensures BST(t)
    ensures NumbersInTree(t) == NumbersInSequence(nums)
{
    t := Empty;
    var i := 0;
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant BST(t)
        invariant NumbersInTree(t) == NumbersInSequence(nums[..i])
    {
        if nums[i] !in NumbersInTree(t) {
            t := InsertBST(t, nums[i]);
        }
        i := i + 1;
    }
}

//IMPL InsertBST
method InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
{
	match t0 
	{
		case Empty => 
            t := Node(x, Empty, Empty);

		case Node(i, left, right) => 
		{
			if x < i
			{
				/* code modified by LLM (iteration 3): Establish BST properties for subtrees */
				LemmaBinarySearchSubtree(i, left, right);
				
				var tmp := InsertBST(left, x);
				t := Node(i, tmp, right);
				
				/* code modified by LLM (iteration 3): Prove BST property is maintained */
				assert BST(tmp);
				assert NumbersInTree(tmp) == NumbersInTree(left) + {x};
				assert forall k :: k in NumbersInTree(tmp) ==> k < i;
				assert forall k :: k in NumbersInTree(right) ==> k > i;
				
				/* code modified by LLM (iteration 3): Prove inorder sequence is ascending */
				var inorder_result := Inorder(tmp) + [i] + Inorder(right);
				assert Inorder(t) == inorder_result;
				
				forall p, q | 0 <= p < q < |inorder_result|
					ensures inorder_result[p] < inorder_result[q]
				{
					var left_size := |Inorder(tmp)|;
					if p < left_size && q < left_size {
						assert BST(tmp);
					} else if p < left_size && q == left_size {
						assert inorder_result[p] in NumbersInTree(tmp);
						assert inorder_result[q] == i;
					} else if p < left_size && q > left_size {
						assert inorder_result[p] in NumbersInTree(tmp);
						assert inorder_result[q] in NumbersInTree(right);
					} else if p == left_size && q > left_size {
						assert inorder_result[p] == i;
						assert inorder_result[q] in NumbersInTree(right);
					} else {
						assert p > left_size && q > left_size;
						assert BST(right);
						var right_inorder := Inorder(right);
						assert inorder_result[p] == right_inorder[p - left_size - 1];
						assert inorder_result[q] == right_inorder[q - left_size - 1];
					}
				}
				
				assert BST(t);
				assert NumbersInTree(t) == NumbersInTree(t0) + {x};
			}
			else
			{
				/* code modified by LLM (iteration 3): Establish BST properties for subtrees */
				LemmaBinarySearchSubtree(i, left, right);
				
				var tmp := InsertBST(right, x);
				t := Node(i, left, tmp);
				
				/* code modified by LLM (iteration 3): Prove BST property is maintained */
				assert BST(tmp);
				assert NumbersInTree(tmp) == NumbersInTree(right) + {x};
				assert forall k :: k in NumbersInTree(left) ==> k < i;
				assert forall k :: k in NumbersInTree(tmp) ==> k > i;
				
				/* code modified by LLM (iteration 3): Prove inorder sequence is ascending */
				var inorder_result := Inorder(left) + [i] + Inorder(tmp);
				assert Inorder(t) == inorder_result;
				
				forall p, q | 0 <= p < q < |inorder_result|
					ensures inorder_result[p] < inorder_result[q]
				{
					var left_size := |Inorder(left)|;
					var right_start := left_size + 1;
					if p < left_size && q < left_size {
						assert BST(left);
					} else if p < left_size && q == left_size {
						assert inorder_result[p] in NumbersInTree(left);
						assert inorder_result[q] == i;
					} else if p < left_size && q >= right_start {
						assert inorder_result[p] in NumbersInTree(left);
						assert inorder_result[q] in NumbersInTree(tmp);
					} else if p == left_size && q >= right_start {
						assert inorder_result[p] == i;
						assert inorder_result[q] in NumbersInTree(tmp);
					} else {
						assert p >= right_start && q >= right_start;
						assert BST(tmp);
						var tmp_inorder := Inorder(tmp);
						assert inorder_result[p] == tmp_inorder[p - right_start];
						assert inorder_result[q] == tmp_inorder[q - right_start];
					}
				}
				
				assert BST(t);
				assert NumbersInTree(t) == NumbersInTree(t0) + {x};
			}
		}
	}
}

//ATOM LemmaBinarySearchSubtree
lemma LemmaBinarySearchSubtree(i: int, left: Tree, right: Tree)
    requires BST(Node(i, left, right))
    ensures BST(left) && BST(right)
    ensures forall k :: k in NumbersInTree(left) ==> k < i
    ensures forall k :: k in NumbersInTree(right) ==> k > i
{
    var inorder_left := Inorder(left);
    var inorder_right := Inorder(right);
    var full_inorder := inorder_left + [i] + inorder_right;
    
    LemmaAscendingSubsequence(full_inorder, 0, |inorder_left|);
    LemmaAscendingSubsequence(full_inorder, |inorder_left| + 1, |full_inorder|);
}

//ATOM LemmaAscendingSubsequence
lemma LemmaAscendingSubsequence(q: seq<int>, start: int, end: int)
    requires 0 <= start <= end <= |q|
    requires Ascending(q)
    ensures Ascending(q[start..end])
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