//ATOM
// Noa Leron 207131871
// Tsuri Farhana 315016907

predicate Sorted(q: seq<int>) {
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

/*
Goal: Implement the well known merge sort algorithm in O(a.Length X log_2(a.Length)) time, recursively.

- Divide the contents of the original array into two local arrays
- After sorting the local arrays (recursively), merge the contents of the two returned arrays using the Merge method (see below)
- DO NOT modify the specification or any other part of the method's signature
- DO NOT introduce any further methods
*/

//ATOM
method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c[..]) && Sorted(d[..])
	ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
{
  assume Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..]);
}

//IMPL 
method MergeSort(a: array<int>) returns (b: array<int>)
	ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
	/* code modified by LLM (iteration 3): Added decreases clause to prove termination */
	decreases a.Length
{
	if a.Length <= 1 {
		b := new int[a.Length];
		if a.Length == 1 {
			b[0] := a[0];
		}
		return;
	}
	
	var mid := a.Length / 2;
	var left := new int[mid];
	var right := new int[a.Length - mid];
	
	/* code modified by LLM (iteration 3): Copy elements to left array */
	var i := 0;
	while i < mid
		invariant 0 <= i <= mid
		invariant forall k :: 0 <= k < i ==> left[k] == a[k]
		modifies left
	{
		left[i] := a[i];
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 3): Copy elements to right array */
	i := 0;
	while i < a.Length - mid
		invariant 0 <= i <= a.Length - mid
		invariant forall k :: 0 <= k < i ==> right[k] == a[mid + k]
		modifies right
	{
		right[i] := a[mid + i];
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 3): Establish multiset properties */
	assert left[..] == a[..mid];
	assert right[..] == a[mid..];
	assert a[..] == a[..mid] + a[mid..];
	assert multiset(a[..]) == multiset(a[..mid]) + multiset(a[mid..]);
	assert multiset(left[..]) + multiset(right[..]) == multiset(a[..]);
	
	/* code modified by LLM (iteration 3): Prove termination conditions */
	assert left.Length < a.Length;
	assert right.Length < a.Length;
	
	var sortedLeft := MergeSort(left);
	var sortedRight := MergeSort(right);
	
	b := new int[a.Length];
	Merge(b, sortedLeft, sortedRight);
	
	/* code modified by LLM (iteration 3): Final multiset proof */
	assert multiset(b[..]) == multiset(sortedLeft[..]) + multiset(sortedRight[..]);
	assert multiset(sortedLeft[..]) == multiset(left[..]);
	assert multiset(sortedRight[..]) == multiset(right[..]);
	assert multiset(b[..]) == multiset(a[..]);
}