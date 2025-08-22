// Noa Leron 207131871
// Tsuri Farhana 315016907

//ATOM 
predicate Sorted(q: seq<int>) {
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

/* code modified by LLM (iteration 4): added helper lemma to establish initial invariant conditions */
lemma InitialInvariantLemma(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c[..]) && Sorted(d[..])
	ensures InvSubSet(b[..], c[..], d[..], 0, 0)
	ensures InvSorted(b[..], c[..], d[..], 0, 0)
{
	// InvSubSet holds because b[..0] == [], c[..0] == [], d[..0] == []
	// and multiset([]) == multiset([]) + multiset([])
	
	// InvSorted holds because Sorted(b[..0]) is trivially true (empty sequence)
	// and the second condition is vacuous since 0 + 0 == 0
}

//IMPL MergeSort
method MergeSort(a: array<int>) returns (b: array<int>)
	ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
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
	
	/* code modified by LLM (iteration 4): added loop invariants for copying elements to left array */
	var i := 0;
	while i < mid
		invariant 0 <= i <= mid
		invariant forall k :: 0 <= k < i ==> left[k] == a[k]
	{
		left[i] := a[i];
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 4): added loop invariants for copying elements to right array */
	i := 0;
	while i < a.Length - mid
		invariant 0 <= i <= a.Length - mid
		invariant forall k :: 0 <= k < i ==> right[k] == a[mid + k]
	{
		right[i] := a[mid + i];
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 4): added assertions to establish multiset relationships */
	assert left[..] == a[..mid];
	assert right[..] == a[mid..];
	assert multiset(a[..]) == multiset(a[..mid]) + multiset(a[mid..]);
	assert multiset(a[..]) == multiset(left[..]) + multiset(right[..]);
	
	var sortedLeft := MergeSort(left);
	var sortedRight := MergeSort(right);
	
	/* code modified by LLM (iteration 4): added assertions to verify properties after recursive calls */
	assert sortedLeft.Length == left.Length == mid;
	assert sortedRight.Length == right.Length == a.Length - mid;
	assert Sorted(sortedLeft[..]) && multiset(sortedLeft[..]) == multiset(left[..]);
	assert Sorted(sortedRight[..]) && multiset(sortedRight[..]) == multiset(right[..]);
	assert multiset(sortedLeft[..]) == multiset(a[..mid]);
	assert multiset(sortedRight[..]) == multiset(a[mid..]);
	
	b := new int[a.Length];
	Merge(b, sortedLeft, sortedRight);
	
	/* code modified by LLM (iteration 4): added final assertions to verify postconditions */
	assert multiset(b[..]) == multiset(sortedLeft[..]) + multiset(sortedRight[..]);
	assert multiset(b[..]) == multiset(a[..mid]) + multiset(a[mid..]);
	assert multiset(b[..]) == multiset(a[..]);
}

//ATOM MergeLoop
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

//ATOM InvSorted
predicate InvSorted(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
{
	i <= |c| && j <= |d| && i + j <= |b| &&
	Sorted(b[..i+j]) &&
	(i + j > 0 ==> 
		(i < |c| ==> b[i+j-1] <= c[i]) &&
		(j < |d| ==> b[i+j-1] <= d[j]))
}

//ATOM InvSubSet  
predicate InvSubSet(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
{
	i <= |c| && j <= |d| && i + j <= |b| &&
	multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
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

//ATOM lemmaInvSubsetTakeValueFromC
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

//ATOM lemmaInvSubsetTakeValueFromD
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

//IMPL Merge
method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c[..]) && Sorted(d[..])
	ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
{
	var i, j := 0, 0;
	
	/* code modified by LLM (iteration 4): establish initial invariants using helper lemma */
	InitialInvariantLemma(b, c, d);
	
	while i + j < b.Length
		invariant i <= c.Length && j <= d.Length && i + j <= b.Length
		invariant InvSubSet(b[..],c[..],d[..],i,j)
		invariant InvSorted(b[..],c[..],d[..],i,j)
		decreases c.Length - i, d.Length - j
	{
		/* code modified by LLM (iteration 4): establish that at least one array has remaining elements */
		assert i + j < b.Length;
		assert b.Length == c.Length + d.Length;
		assert i + j < c.Length + d.Length;
		assert i <= c.Length && j <= d.Length;
		assert i < c.Length || j < d.Length;
		
		i, j := MergeLoop(b, c, d, i, j);
	}
	
	/* code modified by LLM (iteration 4): assert final conditions and prove loop termination */
	assert i + j >= b.Length;
	assert i + j <= b.Length;
	assert i + j == b.Length;
	assert b.Length == c.Length + d.Length;
	assert i <= c.Length && j <= d.Length;
	assert i + j == c.Length + d.Length;
	assert i == c.Length && j == d.Length;
	
	LemmaMultysetsEquals(b[..], c[..], d[..], i, j);
}