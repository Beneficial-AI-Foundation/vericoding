//IMPL 
method Main()
{
}

//ATOM 
predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

//ATOM 
predicate HasAddends(q: seq<int>, x: int)
{
	exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}

//IMPL 
method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
	/* code modified by LLM (iteration 1): fixed initialization with proper bounds */
	i := 0;
	j := |q| - 1;
	
	/* code modified by LLM (iteration 1): corrected loop with proper invariants and termination */
	while q[i] + q[j] != x
		invariant 0 <= i < |q|
		invariant 0 <= j < |q|
		invariant i < j
		invariant HasAddends(q, x)
		invariant exists i',j' :: i <= i' < j' <= j && q[i'] + q[j'] == x
		decreases j - i
	{
		/* code modified by LLM (iteration 1): fixed loop body with proper bounds checking */
		if q[i] + q[j] < x {
			i := i + 1;
		} else {
			j := j - 1;
		}
	}
}

//ATOM 
predicate IsValidIndex<T>(q: seq<T>, i: nat)
{
	0 <= i < |q|
}

//ATOM 
predicate AreOreredIndices<T>(q: seq<T>, i: nat, j: nat)
{
	0 <= i < j < |q|
}

//ATOM 
predicate AreAddendsIndices(q: seq<int>, x: int, i: nat, j: nat)
	requires IsValidIndex(q, i) && IsValidIndex(q, j)
{
	q[i] + q[j] == x
}

//ATOM 
predicate HasAddendsInIndicesRange(q: seq<int>, x: int, i: nat, j: nat)
	requires AreOreredIndices(q, i, j)
{
	HasAddends(q[i..(j + 1)], x)
}

//ATOM 
predicate LoopInv(q: seq<int>, x: int, i: nat, j: nat, sum: int)
{
	AreOreredIndices(q, i, j) &&
	HasAddendsInIndicesRange(q, x, i, j) &&
	AreAddendsIndices(q, sum, i, j)
}

//ATOM 
lemma LoopInvWhenSumIsBigger(q: seq<int>, x: int, i: nat, j: nat, sum: int)
	requires HasAddends(q, x)
	requires Sorted(q)
	requires sum > x;
	requires LoopInv(q, x, i, j, sum)
	ensures HasAddendsInIndicesRange(q, x, i, j - 1)
{
}