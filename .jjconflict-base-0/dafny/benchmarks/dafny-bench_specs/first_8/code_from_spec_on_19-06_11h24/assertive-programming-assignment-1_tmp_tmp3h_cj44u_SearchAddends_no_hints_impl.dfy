method Main()
{
	var q := [1,2,4,5,6,7,10,23];
	var i,j := FindAddends(q, 10);
	print "Searching for addends of 10 in q == [1,2,4,5,6,7,10,23]:\n";
	print "Found that q[";
	print i;
	print "] + q[";
	print j;
	print "] == ";
	print q[i];
	print " + ";
	print q[j];
	print " == 10";
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate HasAddends(q: seq<int>, x: int)
{
	exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}

//IMPL
method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
	i := 0;
	j := |q| - 1;
	
	/* code modified by LLM (iteration 3): simplified loop invariant and fixed bounds checking */
	while q[i] + q[j] != x
		invariant 0 <= i < j < |q|
		invariant exists i',j' :: i <= i' < j' <= j && q[i'] + q[j'] == x
		decreases j - i
	{
		if q[i] + q[j] < x {
			/* code modified by LLM (iteration 3): added bounds check and assertion */
			assert i + 1 < j; // This must hold to maintain invariant
			i := i + 1;
		} else {
			/* code modified by LLM (iteration 3): added bounds check and assertion */
			assert i < j - 1; // This must hold to maintain invariant
			j := j - 1;
		}
	}
}

predicate IsValidIndex<T>(q: seq<T>, i: nat)
{
	0 <= i < |q|
}

predicate AreOreredIndices<T>(q: seq<T>, i: nat, j: nat)
{
	0 <= i < j < |q|
}

predicate AreAddendsIndices(q: seq<int>, x: int, i: nat, j: nat)
	requires IsValidIndex(q, i) && IsValidIndex(q, j)
{
	q[i] + q[j] == x
}

predicate HasAddendsInIndicesRange(q: seq<int>, x: int, i: nat, j: nat)
	requires 0 <= i < j < |q|
{
	exists i',j' :: i <= i' < j' <= j && q[i'] + q[j'] == x
}

predicate LoopInv(q: seq<int>, x: int, i: nat, j: nat, sum: int)
{
	AreOreredIndices(q, i, j) &&
	HasAddendsInIndicesRange(q, x, i, j) &&
	IsValidIndex(q, i) && IsValidIndex(q, j) &&
	AreAddendsIndices(q, sum, i, j)
}

//IMPL
lemma LoopInvWhenSumIsBigger(q: seq<int>, x: int, i: nat, j: nat, sum: int)
	requires HasAddends(q, x)
	requires Sorted(q)
	requires sum > x
	requires LoopInv(q, x, i, j, sum)
	ensures j > 0 && HasAddendsInIndicesRange(q, x, i, j - 1)
{
	/* code modified by LLM (iteration 3): completely rewrote the lemma with correct logic */
	// From LoopInv, we know there exist addends in range [i..j]
	assert HasAddendsInIndicesRange(q, x, i, j);
	var i0, j0 :| i <= i0 < j0 <= j && q[i0] + q[j0] == x;
	
	// From LoopInv, we know sum = q[i] + q[j]
	assert sum == q[i] + q[j];
	assert q[i] + q[j] > x;
	assert q[i0] + q[j0] == x;
	
	// First prove that j > 0
	assert j > j0 >= i0 >= i >= 0;
	
	// Now we need to show that addends exist in range [i, j-1]
	// We know i0, j0 exist with i <= i0 < j0 <= j and q[i0] + q[j0] == x
	
	// Case analysis: either j0 < j or j0 == j
	if j0 == j {
		// If j0 == j, then q[i0] + q[j] == x
		// But we also have q[i] + q[j] > x
		// Since array is sorted and i <= i0, we have q[i] <= q[i0]
		// So q[i0] + q[j] >= q[i] + q[j] > x
		// This contradicts q[i0] + q[j] == x
		assert q[i] <= q[i0]; // from sorted property
		assert q[i0] + q[j] >= q[i] + q[j]; // from monotonicity
		assert q[i0] + q[j] > x; // from transitivity
		assert false; // contradiction with q[i0] + q[j] == x
	}
	
	// Therefore j0 < j
	assert j0 < j;
	assert j0 <= j - 1;
	
	// Now check if we can form the range [i, j-1]
	if i < j - 1 {
		// We have i <= i0 < j0 <= j-1, so addends exist in [i, j-1]
		assert HasAddendsInIndicesRange(q, x, i, j - 1);
	} else {
		// If i >= j - 1, then since i < j (from LoopInv), we must have i == j - 1
		// But then i0 < j0 with i <= i0 < j0 <= j-1 = i is impossible
		assert i < j; // from LoopInv
		assert i == j - 1; // only possibility
		assert i <= i0 < j0 <= j - 1 == i;
		assert i0 < i && i0 >= i; // contradiction
		assert false;
	}
}