// IMPL 
method Main()
{
}


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


// IMPL 

method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
	i := 0;
	j := |q| - 1;
	
	/* code modified by LLM (iteration 1): Added assertion to establish initial invariant */
	EstablishInitialInvariant(q, x);
	
	while i < j
		invariant 0 <= i < j < |q|
		/* code modified by LLM (iteration 1): Strengthened invariant to maintain existence of solution in current range */
		invariant exists ii, jj :: i <= ii < jj <= j && q[ii] + q[jj] == x
		/* code modified by LLM (iteration 1): Added decreasing clause for termination */
		decreases j - i
	{
		var sum := q[i] + q[j];
		if sum == x {
			return;
		} else if sum < x {
			/* code modified by LLM (iteration 1): Added helper lemma call to prove invariant preservation */
			PreserveSolutionWhenIncrementI(q, x, i, j);
			i := i + 1;
		} else {
			/* code modified by LLM (iteration 1): Added helper lemma call to prove invariant preservation */
			PreserveSolutionWhenDecrementJ(q, x, i, j);
			j := j - 1;
		}
	}
}

/* code modified by LLM (iteration 1): Added lemma to establish initial invariant */
lemma EstablishInitialInvariant(q: seq<int>, x: int)
	requires HasAddends(q, x)
	requires |q| >= 2
	ensures exists ii, jj :: 0 <= ii < jj <= |q|-1 && q[ii] + q[jj] == x
{
	var ii, jj :| 0 <= ii < jj < |q| && q[ii] + q[jj] == x;
	assert 0 <= ii < jj <= |q|-1 && q[ii] + q[jj] == x;
}

/* code modified by LLM (iteration 1): Fixed helper lemma to prove solution exists when incrementing i */
lemma PreserveSolutionWhenIncrementI(q: seq<int>, x: int, i: nat, j: nat)
	requires Sorted(q)
	requires 0 <= i < j < |q|
	requires exists ii, jj :: i <= ii < jj <= j && q[ii] + q[jj] == x
	requires q[i] + q[j] < x
	ensures exists ii, jj :: i+1 <= ii < jj <= j && q[ii] + q[jj] == x
{
	/* code modified by LLM (iteration 1): Fixed proof logic */
	var ii, jj :| i <= ii < jj <= j && q[ii] + q[jj] == x;
	if ii == i {
		// Since q is sorted and jj <= j, we have q[jj] <= q[j]
		// So q[i] + q[jj] <= q[i] + q[j] < x
		// But we also have q[ii] + q[jj] = q[i] + q[jj] = x
		// This is a contradiction
		assert q[i] + q[jj] <= q[i] + q[j];
		assert q[i] + q[j] < x;
		assert q[i] + q[jj] = x;
		assert false;
	}
	// So ii > i, which means ii >= i+1
	assert i+1 <= ii < jj <= j && q[ii] + q[jj] == x;
}

/* code modified by LLM (iteration 1): Fixed helper lemma to prove solution exists when decrementing j */
lemma PreserveSolutionWhenDecrementJ(q: seq<int>, x: int, i: nat, j: nat)
	requires Sorted(q)
	requires 0 <= i < j < |q|
	requires exists ii, jj :: i <= ii < jj <= j && q[ii] + q[jj] == x
	requires q[i] + q[j] > x
	ensures exists ii, jj :: i <= ii < jj <= j-1 && q[ii] + q[jj] == x
{
	/* code modified by LLM (iteration 1): Fixed proof logic */
	var ii, jj :| i <= ii < jj <= j && q[ii] + q[jj] == x;
	if jj == j {
		// Since q is sorted and ii >= i, we have q[ii] >= q[i]
		// So q[ii] + q[j] >= q[i] + q[j] > x
		// But we also have q[ii] + q[jj] = q[ii] + q[j] = x
		// This is a contradiction
		assert q[ii] + q[j] >= q[i] + q[j];
		assert q[i] + q[j] > x;
		assert q[ii] + q[j] = x;
		assert false;
	}
	// So jj < j, which means jj <= j-1
	assert i <= ii < jj <= j-1 && q[ii] + q[jj] == x;
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