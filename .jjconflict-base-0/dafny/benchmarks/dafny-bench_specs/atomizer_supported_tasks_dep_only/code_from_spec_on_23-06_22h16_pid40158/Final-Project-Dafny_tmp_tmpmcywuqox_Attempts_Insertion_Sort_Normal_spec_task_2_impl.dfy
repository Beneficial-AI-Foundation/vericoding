// ATOM 
predicate sorted (a: array<int>)
	reads a
{
	sortedA(a, a.Length)
}

// ATOM 
predicate sortedA (a: array<int>, i: int)
	requires 0 <= i <= a.Length
	reads a
{
	forall k :: 0 < k < i ==> a[k-1] <= a[k]
}

//IMPL lookForMin
method lookForMin (a: array<int>, i: int) returns (m: int)
	requires 0 <= i < a.Length
	ensures i <= m < a.Length
	ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{
	m := i;
	var j := i + 1;
	while j < a.Length
		invariant i <= m < a.Length
		invariant i <= j <= a.Length
		invariant forall k :: i <= k < j ==> a[k] >= a[m]
	{
		if a[j] < a[m] {
			m := j;
		}
		j := j + 1;
	}
}

//IMPL insertionSort
method insertionSort (a: array<int>)
	modifies a
	ensures sorted(a)
{
	var i := 1;
	while i < a.Length
		invariant 0 <= i <= a.Length
		invariant sortedA(a, i)
	{
		var key := a[i];
		var j := i - 1;
		/* code modified by LLM (iteration 1): Simplified invariants to track the shifting correctly */
		while j >= 0 && a[j] > key
			invariant -1 <= j < i
			invariant forall k :: j + 2 <= k <= i ==> a[k] > key
			invariant forall k :: 0 <= k <= j ==> a[k] <= a[k+1]
			invariant sortedA(a, j + 1)
		{
			a[j + 1] := a[j];
			j := j - 1;
		}
		a[j + 1] := key;
		/* code modified by LLM (iteration 1): Added assertion to help prove sortedA(a, i+1) */
		assert sortedA(a, i + 1);
		i := i + 1;
	}
}