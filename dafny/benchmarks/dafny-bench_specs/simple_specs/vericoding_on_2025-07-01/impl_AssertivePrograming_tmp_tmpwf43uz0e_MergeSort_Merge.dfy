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
	
	while k < b.Length
		invariant 0 <= i <= c.Length
		invariant 0 <= j <= d.Length
		invariant k == i + j
		invariant k <= b.Length
		invariant Sorted(b[..k])
		invariant multiset(b[..k]) == multiset(c[..i]) + multiset(d[..j])
		invariant i < c.Length && j < d.Length ==> c[i] <= b[k-1] || d[j] <= b[k-1]
		invariant i < c.Length && j == d.Length ==> forall x :: x in multiset(d[..]) ==> x <= c[i]
		invariant j < d.Length && i == c.Length ==> forall x :: x in multiset(c[..]) ==> x <= d[j]
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
}