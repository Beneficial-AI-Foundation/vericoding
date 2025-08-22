// Noa Leron 207131871
// Tsuri Farhana 315016907

//ATOM 
predicate Sorted(q: seq<int>) {
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

//IMPL Merge
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
		invariant multiset(b[..k]) == multiset(c[..i]) + multiset(d[..j])
		invariant Sorted(b[..k])
		/* code modified by LLM (iteration 4): Simplified invariants for sortedness maintenance */
		invariant k > 0 && i < c.Length ==> b[k-1] <= c[i]
		invariant k > 0 && j < d.Length ==> b[k-1] <= d[j]
	{
		if i == c.Length {
			/* code modified by LLM (iteration 4): Copy remaining elements from d */
			b[k] := d[j];
			j := j + 1;
		} else if j == d.Length {
			/* code modified by LLM (iteration 4): Copy remaining elements from c */
			b[k] := c[i];
			i := i + 1;
		} else if c[i] <= d[j] {
			/* code modified by LLM (iteration 4): Take smaller element from c */
			b[k] := c[i];
			i := i + 1;
		} else {
			/* code modified by LLM (iteration 4): Take smaller element from d */
			b[k] := d[j];
			j := j + 1;
		}
		k := k + 1;
	}
}

//ATOM 
lemma LemmaMultysetsEquals (b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
	requires i == |c|;
	requires j == |d|;
	requires i + j == |b|;
	requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
	ensures multiset(b[..]) == multiset(c[..])+multiset(d[..]);
	{
	}

//ATOM 
predicate InvSubSet(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
{
	i <= |c| && j <= |d| && i + j <= |b| && |c| + |d| == |b| &&
	multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
}

//ATOM 
predicate InvSorted(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
{
	Sorted(b[..i+j]) &&
	(i+j > 0 ==> (
		(i < |c| ==> c[i] >= b[i+j-1]) &&
		(j < |d| ==> d[j] >= b[i+j-1])
	))
}

//ATOM 
method MergeLoop(b: array<int>, c: array<int>, d: array<int>,i0: nat , j0: nat)  returns (i: nat, j: nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c[..]) && Sorted(d[..])
	requires i0 <= c.Length && j0 <= d.Length && i0 + j0 <= b.Length
	requires InvSubSet(b[..],c[..],d[..],i0,j0)
	requires InvSorted(b[..],c[..],d[..],i0,j0)
	requires i0 + j0 < b.Length

	modifies b

	ensures i <= c.Length && j <= d.Length && i + j <= b.Length
	ensures InvSubSet(b[..],c[..],d[..],i,j)
	ensures InvSorted(b[..],c[..],d[..],i,j)
	ensures 0 <= c.Length - i < c.Length - i0 || (c.Length - i == c.Length - i0 && 0 <= d.Length - j < d.Length - j0)
{
	i,j := i0,j0;
		
	if(i == c.Length || (j< d.Length && d[j] < c[i])){
		b[i+j] := d[j];
		lemmaInvSubsetTakeValueFromD(b[..],c[..],d[..],i,j);
		j := j + 1;
	}
	else{
		b[i+j] := c[i];
		lemmaInvSubsetTakeValueFromC(b[..],c[..],d[..],i,j);
		i := i + 1;
	}
}

//ATOM 
lemma lemmaInvSubsetTakeValueFromC (b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
	requires i < |c|;
	requires j <= |d|;
	requires i + j < |b|;
	requires |c| + |d| == |b|;
	requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
	requires b[i+j] == c[i]
	ensures multiset(b[..i+j+1]) == multiset(c[..i+1])+multiset(d[..j])
{
}

//ATOM 
lemma lemmaInvSubsetTakeValueFromD (b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
	requires i <= |c|;
	requires j < |d|;
	requires i + j < |b|;
	requires |c| + |d| == |b|;
	requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
	requires b[i+j] == d[j]
	ensures multiset(b[..i+j+1]) == multiset(c[..i])+multiset(d[..j+1])
{
}

//ATOM 
method Main() {
}