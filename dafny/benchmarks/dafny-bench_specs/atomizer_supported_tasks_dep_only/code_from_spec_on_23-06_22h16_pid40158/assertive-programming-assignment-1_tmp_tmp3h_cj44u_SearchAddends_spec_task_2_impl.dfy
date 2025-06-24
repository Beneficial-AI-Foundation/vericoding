//ATOM_PLACEHOLDER_Main

// ATOM 

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}


// ATOM 

predicate HasAddends(q: seq<int>, x: int)
{
	exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}


//IMPL FindAddends

method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
	i := 0;
	j := |q| - 1;
	
	/* code modified by LLM (iteration 1): simplified loop invariant and added helper lemmas for maintaining invariant */
	while q[i] + q[j] != x
		invariant 0 <= i < j < |q|
		invariant exists a, b :: i <= a < b <= j && q[a] + q[b] == x
		decreases j - i
	{
		var sum := q[i] + q[j];
		if sum < x {
			/* code modified by LLM (iteration 1): added lemma call to prove invariant maintenance */
			PreservesExistenceWhenIncrementingI(q, x, i, j);
			i := i + 1;
		} else {
			/* code modified by LLM (iteration 1): added lemma call to prove invariant maintenance */
			PreservesExistenceWhenDecrementingJ(q, x, i, j);
			j := j - 1;
		}
	}
}

/* code modified by LLM (iteration 1): added helper lemma for when sum is too small */
lemma PreservesExistenceWhenIncrementingI(q: seq<int>, x: int, i: nat, j: nat)
	requires Sorted(q)
	requires 0 <= i < j < |q|
	requires exists a, b :: i <= a < b <= j && q[a] + q[b] == x
	requires q[i] + q[j] < x
	ensures exists a, b :: (i+1) <= a < b <= j && q[a] + q[b] == x
{
	var a, b :| i <= a < b <= j && q[a] + q[b] == x;
	if a == i {
		// If a == i, then q[i] + q[b] == x, but we know q[i] + q[j] < x
		// Since q is sorted and b <= j, we have q[b] <= q[j]
		// This would imply q[i] + q[b] <= q[i] + q[j] < x, contradicting q[i] + q[b] == x
		assert q[b] <= q[j]; // from sortedness
		assert q[i] + q[b] <= q[i] + q[j]; // arithmetic
		assert q[i] + q[b] < x; // from above and precondition
		assert false; // contradiction with q[a] + q[b] == x
	}
	// If a > i, then a >= i+1, so the pair (a,b) satisfies the postcondition
	assert a >= i + 1;
}

/* code modified by LLM (iteration 1): added helper lemma for when sum is too big */
lemma PreservesExistenceWhenDecrementingJ(q: seq<int>, x: int, i: nat, j: nat)
	requires Sorted(q)
	requires 0 <= i < j < |q|
	requires exists a, b :: i <= a < b <= j && q[a] + q[b] == x
	requires q[i] + q[j] > x
	ensures exists a, b :: i <= a < b <= (j-1) && q[a] + q[b] == x
{
	var a, b :| i <= a < b <= j && q[a] + q[b] == x;
	if b == j {
		// If b == j, then q[a] + q[j] == x, but we know q[i] + q[j] > x
		// Since q is sorted and a >= i, we have q[a] >= q[i]
		// This would imply q[a] + q[j] >= q[i] + q[j] > x, contradicting q[a] + q[j] == x
		assert q[a] >= q[i]; // from sortedness
		assert q[a] + q[j] >= q[i] + q[j]; // arithmetic
		assert q[a] + q[j] > x; // from above and precondition
		assert false; // contradiction with q[a] + q[b] == x
	}
	// If b < j, then b <= j-1, so the pair (a,b) satisfies the postcondition
	assert b <= j - 1;
}


// ATOM 

predicate IsValidIndex<T>(q: seq<T>, i: nat)
{
	0 <= i < |q|
}


// ATOM 

predicate AreOreredIndices<T>(q: seq<T>, i: nat, j: nat)
{
	0 <= i < j < |q|
}


// ATOM 

predicate AreAddendsIndices(q: seq<int>, x: int, i: nat, j: nat)
	requires IsValidIndex(q, i) && IsValidIndex(q, j)
{
	q[i] + q[j] == x
}


// ATOM 

predicate HasAddendsInIndicesRange(q: seq<int>, x: int, i: nat, j: nat)
	requires AreOreredIndices(q, i, j)
{
	HasAddends(q[i..(j + 1)], x)
}


// ATOM 

predicate LoopInv(q: seq<int>, x: int, i: nat, j: nat, sum: int)
{
	AreOreredIndices(q, i, j) &&
	HasAddendsInIndicesRange(q, x, i, j) &&
	AreAddendsIndices(q, sum, i, j)
}


// ATOM 

lemma LoopInvWhenSumIsBigger(q: seq<int>, x: int, i: nat, j: nat, sum: int)
	requires HasAddends(q, x)
	requires Sorted(q)
	requires sum > x;
	requires LoopInv(q, x, i, j, sum)
	ensures HasAddendsInIndicesRange(q, x, i, j - 1)
{
}