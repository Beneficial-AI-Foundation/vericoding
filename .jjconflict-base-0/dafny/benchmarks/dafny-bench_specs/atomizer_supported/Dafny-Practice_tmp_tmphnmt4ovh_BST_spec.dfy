// ATOM 
datatype Tree = Empty | Node(int,Tree,Tree)
// SPEC 

method Main() {
}


// SPEC 

method PrintTreeNumbersInorder(t: Tree)
{
}


// ATOM 

function NumbersInTree(t: Tree): set<int>
{
	NumbersInSequence(Inorder(t))
}


// ATOM 

function NumbersInSequence(q: seq<int>): set<int>
{
	set x | x in q
}


// ATOM 

predicate BST(t: Tree)
{
	Ascending(Inorder(t))
}


// ATOM 

function Inorder(t: Tree): seq<int>
{
	match t {
		case Empty => []
		case Node(n',nt1,nt2) => Inorder(nt1)+[n']+Inorder(nt2)
	}
}


// ATOM 

predicate Ascending(q: seq<int>)
{
	forall i,j :: 0 <= i < j < |q| ==> q[i] < q[j]
}


// ATOM 

predicate NoDuplicates(q: seq<int>) { forall i,j :: 0 <= i < j < |q| ==> q[i] != q[j] }

/*
	Goal: Implement correctly, clearly. No need to document the proof obligations.
*/


/*
	Goal: Implement correctly, clearly. No need to document the proof obligations.
*/
// SPEC 
method BuildBST(q: seq<int>) returns (t: Tree)
	requires NoDuplicates(q)
	ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
}

/*
	Goal: Implement correctly, efficiently, clearly, documenting the proof obligations
	as we've learned, with assertions and a lemma for each proof goal
*/


/*
	Goal: Implement correctly, efficiently, clearly, documenting the proof obligations
	as we've learned, with assertions and a lemma for each proof goal
*/
// SPEC 
method InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{
}
{
}

{
	match t0 
	{
		case Empty => t := Node(x, Empty, Empty);

		case Node(i, left, right) => 
		{
			var tmp:Tree:= Empty;
			if x < i
			{
				LemmaBinarySearchSubtree(i,left,right);
				tmp :=  InsertBST(left, x);
				t := Node(i, tmp, right);
				ghost var right_nums := Inorder(right);
				ghost var left_nums := Inorder(left);
				ghost var all_nums := Inorder(t0);
				// assert all_nums[..|left_nums|] == left_nums;
				ghost var new_all_nums := Inorder(t);
				ghost var new_left_nums := Inorder(tmp);
				// assert Ascending(new_left_nums+ [i] + right_nums);



				
				
				lemma_all_small(new_left_nums,i);
				

			}
			else
			{
				LemmaBinarySearchSubtree(i,left,right);
				tmp := InsertBST(right, x);
				t := Node(i, left, tmp);

				ghost var right_nums := Inorder(right);
				ghost var left_nums := Inorder(left);
				ghost var all_nums := Inorder(t0);
				// assert all_nums[..|left_nums|] == left_nums;
				ghost var new_all_nums := Inorder(t);
				ghost var new_right_nums := Inorder(tmp);
				// assert Ascending(left_nums+ [i] + right_nums);


				// assert forall j :: j in NumbersInSequence(all_nums[|left_nums|+1..]) ==> j > i;
				// assert forall j :: j in NumbersInSequence(all_nums[|left_nums|+1..])+{x} ==> j > i;
				
				
				lemma_all_big(new_right_nums,i);
				
				// assert Ascending(new_right_nums+[i]);

			}
		}
	}
}

// ATOM 

lemma	LemmaBinarySearchSubtree(n: int, left: Tree, right: Tree)
	requires BST(Node(n, left, right))
	ensures BST(left) && BST(right)
{
	var qleft, qright := Inorder(left), Inorder(right);
	var q := qleft+[n]+qright;
}


// ATOM 

lemma LemmaAscendingSubsequence(q1: seq<int>, q2: seq<int>, i: nat)
	requires i <= |q1|-|q2| && q2 == q1[i..i+|q2|]
	requires Ascending(q1)
	ensures Ascending(q2)
{}


 lemma_all_small(q:seq<int>,i:int)
	requires forall k:: k in NumbersInSequence(q) ==> k < i
	requires forall k:: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
	ensures forall j::0<=j < |q| ==> q[j] < i
{}

 lemma_all_big(q:seq<int>,i:int)
	requires forall k:: k in NumbersInSequence(q) ==> k > i
	requires forall k:: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
	ensures forall j::0<=j < |q| ==> q[j] > i
{}
 lemma_all_big(q:seq<int>,i:int)
	requires forall k:: k in NumbersInSequence(q) ==> k > i
	requires forall k:: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
	ensures forall j::0<=j < |q| ==> q[j] > i
{}
