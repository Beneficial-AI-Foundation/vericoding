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


//IMPL SPEC
method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c[..]) && Sorted(d[..])
	ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
{
	var i := 0; // index for array c;
	var j := 0; // index for array d;
	var k := 0; // index for array b;
	
	// Merge elements from c and d into b
	while k < b.Length
		invariant 0 <= i <= c.Length && 0 <= j <= d.Length && 0 <= k <= b.Length
		invariant i + j == k
		/* code modified by LLM (iteration 3): Fixed multiset invariant and added stronger sortedness invariants, removed problematic suffix invariant */
		invariant multiset(b[..k]) == multiset(c[..i]) + multiset(d[..j])
		invariant Sorted(b[..k])
		invariant k > 0 && i < c.Length ==> b[k-1] <= c[i]
		invariant k > 0 && j < d.Length ==> b[k-1] <= d[j]
	{
		if i == c.Length {
			b[k] := d[j];
			j := j + 1;
		} else if j == d.Length {
			b[k] := c[i];
			i := i + 1;
		} else if c[i] <= d[j] {
			b[k] := c[i];
			i := i + 1;
		} else {
			b[k] := d[j];
			j := j + 1;
		}
		k := k + 1;
	}
	
	/* code modified by LLM (iteration 3): Added assertion to help Dafny prove postcondition */
	assert k == b.Length && i == c.Length && j == d.Length;
	assert b[..k] == b[..];
	assert c[..i] == c[..] && d[..j] == d[..];
}