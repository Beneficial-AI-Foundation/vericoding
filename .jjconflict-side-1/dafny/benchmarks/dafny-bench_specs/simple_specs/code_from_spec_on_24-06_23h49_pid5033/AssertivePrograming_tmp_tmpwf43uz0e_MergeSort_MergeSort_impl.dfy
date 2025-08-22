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


//IMPL MergeSort
method MergeSort(a: array<int>) returns (b: array<int>)
	ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
	/* code modified by LLM (iteration 4): added decreases clause for termination */
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
	
	var i := 0;
	/* code modified by LLM (iteration 4): improved loop invariants for array copying */
	while i < mid
		invariant 0 <= i <= mid
		invariant forall j :: 0 <= j < i ==> left[j] == a[j]
		modifies left
	{
		left[i] := a[i];
		i := i + 1;
	}
	
	i := 0;
	/* code modified by LLM (iteration 4): improved loop invariants for array copying */
	while i < a.Length - mid
		invariant 0 <= i <= a.Length - mid
		invariant forall j :: 0 <= j < i ==> right[j] == a[mid + j]
		modifies right
	{
		right[i] := a[mid + i];
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 4): added comprehensive assertions to establish sequence and multiset relationships */
	assert forall j :: 0 <= j < mid ==> left[j] == a[j];
	assert forall j :: 0 <= j < a.Length - mid ==> right[j] == a[mid + j];
	assert left[..] == a[..mid];
	assert right[..] == a[mid..];
	assert a[..] == a[..mid] + a[mid..];
	assert multiset(a[..]) == multiset(a[..mid]) + multiset(a[mid..]);
	assert multiset(left[..]) + multiset(right[..]) == multiset(a[..]);
	
	/* code modified by LLM (iteration 4): added termination size assertions before recursive calls */
	assert left.Length < a.Length;
	assert right.Length < a.Length;
	
	var sortedLeft := MergeSort(left);
	var sortedRight := MergeSort(right);
	
	/* code modified by LLM (iteration 4): strengthened assertions about recursive call results */
	assert sortedLeft.Length == left.Length == mid;
	assert sortedRight.Length == right.Length == a.Length - mid;
	assert Sorted(sortedLeft[..]) && multiset(sortedLeft[..]) == multiset(left[..]);
	assert Sorted(sortedRight[..]) && multiset(sortedRight[..]) == multiset(right[..]);
	assert multiset(sortedLeft[..]) == multiset(left[..]);
	assert multiset(sortedRight[..]) == multiset(right[..]);
	assert multiset(left[..]) + multiset(right[..]) == multiset(a[..]);
	assert multiset(sortedLeft[..]) + multiset(sortedRight[..]) == multiset(a[..]);
	assert sortedLeft.Length + sortedRight.Length == a.Length;
	
	b := new int[a.Length];
	/* code modified by LLM (iteration 4): added assertion before Merge call to verify preconditions */
	assert b != sortedLeft && b != sortedRight;
	assert b.Length == sortedLeft.Length + sortedRight.Length;
	assert Sorted(sortedLeft[..]) && Sorted(sortedRight[..]);
	
	Merge(b, sortedLeft, sortedRight);
	
	/* code modified by LLM (iteration 4): added final assertion chain to help verify postconditions */
	assert Sorted(b[..]);
	assert multiset(b[..]) == multiset(sortedLeft[..]) + multiset(sortedRight[..]);
	assert multiset(b[..]) == multiset(left[..]) + multiset(right[..]);
	assert multiset(b[..]) == multiset(a[..]);
	assert b.Length == a.Length;
}