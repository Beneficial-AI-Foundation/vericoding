//ATOM

predicate sorted' (a: array<int>, i: int)
	requires a != null
	requires 0 <= i <= a.Length
	reads a
{
	forall k :: 0 < k < i ==> a[k-1] <= a[k]
}

/* code modified by LLM (iteration 1): Added sorted predicate and helper predicates for selection sort */
predicate sorted(a: array<int>)
	requires a != null
	reads a
{
	forall k :: 0 < k < a.Length ==> a[k-1] <= a[k]
}

predicate partitioned(a: array<int>, i: int)
	requires a != null
	requires 0 <= i <= a.Length
	reads a
{
	forall j, k :: 0 <= j < i <= k < a.Length ==> a[j] <= a[k]
}

method findMin(a: array<int>, start: int) returns (minIndex: int)
	requires a != null
	requires 0 <= start < a.Length
	ensures start <= minIndex < a.Length
	ensures forall k :: start <= k < a.Length ==> a[minIndex] <= a[k]
{
	minIndex := start;
	var i := start + 1;
	while i < a.Length
		invariant start <= minIndex < a.Length
		invariant start + 1 <= i <= a.Length
		invariant forall k :: start <= k < i ==> a[minIndex] <= a[k]
	{
		if a[i] < a[minIndex] {
			minIndex := i;
		}
		i := i + 1;
	}
}

// SPEC

// Selection sort on arrays

method SelectionSort(a: array<int>) 
 modifies a
 ensures sorted(a)
 //ensures multiset(old(a[..])) == multiset(a[..])
{
	/* code modified by LLM (iteration 1): Complete selection sort implementation */
	if a.Length <= 1 {
		return;
	}
	
	var i := 0;
	while i < a.Length - 1
		invariant 0 <= i <= a.Length - 1
		invariant sorted'(a, i)
		invariant partitioned(a, i)
	{
		var minIndex := findMin(a, i);
		
		// Swap a[i] and a[minIndex]
		var temp := a[i];
		a[i] := a[minIndex];
		a[minIndex] := temp;
		
		i := i + 1;
	}
}