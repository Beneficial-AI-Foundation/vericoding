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
	var i, j, k := 0, 0, 0;
	
	while k < b.Length
		invariant 0 <= i <= c.Length && 0 <= j <= d.Length && 0 <= k <= b.Length
		invariant k == i + j
		invariant Sorted(b[0..k])
		invariant multiset(b[0..k]) == multiset(c[0..i]) + multiset(d[0..j])
		invariant k > 0 && i < c.Length && j < d.Length ==> b[k-1] <= c[i] && b[k-1] <= d[j]
		/* code modified by LLM (iteration 4): Fixed boundary condition invariants */
		invariant i == c.Length ==> j < d.Length || k == b.Length
		invariant j == d.Length ==> i < c.Length || k == b.Length
	{
		if i == c.Length {
			b[k] := d[j];
			/* code modified by LLM (iteration 4): Establish sorted property when copying from d */
			if k > 0 {
				// We know from invariant that when i == c.Length and k > 0, we have b[k-1] <= d[j]
				// Or if this is the first element from d after c elements, c and d are sorted
				if j > 0 {
					assert Sorted(d[0..j+1]); // d is sorted, so d[j-1] <= d[j]
				}
			}
			j := j + 1;
		} else if j == d.Length {
			b[k] := c[i];
			/* code modified by LLM (iteration 4): Establish sorted property when copying from c */
			if k > 0 {
				// We know from invariant that when j == d.Length and k > 0, we have b[k-1] <= c[i]  
				// Or if this is the first element from c after d elements, c and d are sorted
				if i > 0 {
					assert Sorted(c[0..i+1]); // c is sorted, so c[i-1] <= c[i]
				}
			}
			i := i + 1;
		} else if c[i] <= d[j] {
			b[k] := c[i];
			/* code modified by LLM (iteration 4): Establish sorted property for merge case */
			if k > 0 {
				// From loop invariant: b[k-1] <= c[i] when both i,j < respective lengths
				assert b[k-1] <= c[i];
			}
			i := i + 1;
		} else {
			b[k] := d[j];
			/* code modified by LLM (iteration 4): Establish sorted property for merge case */
			if k > 0 {
				// From loop invariant: b[k-1] <= d[j] when both i,j < respective lengths
				// Since c[i] > d[j] and b[k-1] <= c[i], we have b[k-1] <= d[j]
				assert c[i] > d[j];
				assert b[k-1] <= c[i];
				assert b[k-1] <= d[j];
			}
			j := j + 1;
		}
		k := k + 1;
	}
}