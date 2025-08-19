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

//IMPL 
method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c[..]) && Sorted(d[..])
	ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
{
	var i := 0;
	var j := 0;
	var k := 0;
	
	/* code modified by LLM (iteration 1): fixed loop invariants to properly establish sortedness and multiset preservation */
	while k < b.Length
		invariant 0 <= i <= c.Length
		invariant 0 <= j <= d.Length
		invariant k == i + j
		invariant k <= b.Length
		invariant Sorted(b[..k])
		invariant multiset(b[..k]) == multiset(c[..i]) + multiset(d[..j])
		invariant forall x :: 0 <= x < k && i < c.Length ==> b[x] <= c[i]
		invariant forall x :: 0 <= x < k && j < d.Length ==> b[x] <= d[j]
		invariant i == c.Length ==> j < d.Length
		invariant j == d.Length ==> i < c.Length
	{
		/* code modified by LLM (iteration 1): added assertions to help verification understand the merge logic */
		if i == c.Length {
			assert j < d.Length;
			b[k] := d[j];
			j := j + 1;
		} else if j == d.Length {
			assert i < c.Length;
			b[k] := c[i];
			i := i + 1;
		} else if c[i] <= d[j] {
			assert i < c.Length && j < d.Length;
			b[k] := c[i];
			i := i + 1;
		} else {
			assert i < c.Length && j < d.Length;
			assert d[j] < c[i];
			b[k] := d[j];
			j := j + 1;
		}
		k := k + 1;
	}
	
	/* code modified by LLM (iteration 1): added final assertions to establish postconditions */
	assert i == c.Length && j == d.Length;
	assert k == b.Length;
	assert multiset(b[..]) == multiset(c[..]) + multiset(d[..]);
}