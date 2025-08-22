//ATOM
predicate Sorted(q: seq<int>) {
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

//IMPL
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
	
	var i := 0;
	while i < mid
		invariant 0 <= i <= mid
		invariant forall k :: 0 <= k < i ==> left[k] == a[k]
	{
		left[i] := a[i];
		i := i + 1;
	}
	
	i := 0;
	while i < a.Length - mid
		invariant 0 <= i <= a.Length - mid
		invariant forall k :: 0 <= k < i ==> right[k] == a[mid + k]
	{
		right[i] := a[mid + i];
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 4): added assertions to establish array equality and multiset properties */
	assert left[..] == a[..mid];
	assert right[..] == a[mid..];
	assert multiset(a[..]) == multiset(a[..mid]) + multiset(a[mid..]);
	assert multiset(left[..]) == multiset(a[..mid]);
	assert multiset(right[..]) == multiset(a[mid..]);
	
	var leftSorted := MergeSort(left);
	var rightSorted := MergeSort(right);
	
	/* code modified by LLM (iteration 4): assertions to maintain multiset equality through recursive calls */
	assert multiset(leftSorted[..]) == multiset(left[..]) == multiset(a[..mid]);
	assert multiset(rightSorted[..]) == multiset(right[..]) == multiset(a[mid..]);
	assert multiset(leftSorted[..]) + multiset(rightSorted[..]) == multiset(a[..]);
	
	b := new int[a.Length];
	Merge(b, leftSorted, rightSorted);
}

//ATOM
ghost predicate Inv(a: seq<int>, a1: seq<int>, a2: seq<int>, i: nat, mid: nat){
    (i <= |a1|) && (i <= |a2|) && (i+mid <= |a|) &&
    (a1[..i] == a[..i]) && (a2[..i] == a[mid..(i+mid)])
}

//IMPL
method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c[..]) && Sorted(d[..])
	ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
{
	var i, j := 0, 0;
	
	/* code modified by LLM (iteration 4): establish initial invariant base case */
	assert InvSubSet(b[..], c[..], d[..], i, j);
	assert InvSorted(b[..], c[..], d[..], i, j);
	
	while i + j < b.Length
		invariant i <= c.Length && j <= d.Length && i + j <= b.Length
		invariant InvSubSet(b[..],c[..],d[..],i,j)
		invariant InvSorted(b[..],c[..],d[..],i,j)
	{
		if i >= c.Length {
			b[i + j] := d[j];
			lemmaInvSubsetTakeValueFromD(b[..], c[..], d[..], i, j);
			lemmaInvSortedTakeValueFromD(b[..], c[..], d[..], i, j);
			j := j + 1;
		} else if j >= d.Length {
			b[i + j] := c[i];
			lemmaInvSubsetTakeValueFromC(b[..], c[..], d[..], i, j);
			lemmaInvSortedTakeValueFromC(b[..], c[..], d[..], i, j);
			i := i + 1;
		} else {
			i, j := MergeLoop(b, c, d, i, j);
		}
	}
	
	LemmaMultysetsEquals(b[..], c[..], d[..], i, j);
}

//IMPL
method MergeLoop(b: array<int>, c: array<int>, d: array<int>,i0: nat , j0: nat)  returns (i: nat, j: nat)
		requires b != c && b != d && b.Length == c.Length + d.Length
		requires Sorted(c[..]) && Sorted(d[..])
		requires i0 <= c.Length && j0 <= d.Length && i0 + j0 <= b.Length
		requires InvSubSet(b[..],c[..],d[..],i0,j0)
		requires InvSorted(b[..],c[..],d[..],i0,j0)
		requires i0 + j0 < b.Length
		requires i0 < c.Length && j0 < d.Length

		modifies b

		ensures i <= c.Length && j <= d.Length && i + j <= b.Length
		ensures InvSubSet(b[..],c[..],d[..],i,j)
		ensures InvSorted(b[..],c[..],d[..],i,j)
		ensures 0 <= c.Length - i < c.Length - i0 || (c.Length - i == c.Length - i0 && 0 <= d.Length - j < d.Length - j0)
{
	i := i0;
	j := j0;
	
	if c[i] <= d[j] {
		b[i + j] := c[i];
		lemmaInvSubsetTakeValueFromC(b[..], c[..], d[..], i, j);
		lemmaInvSortedTakeValueFromC(b[..], c[..], d[..], i, j);
		i := i + 1;
	} else {
		b[i + j] := d[j];
		lemmaInvSubsetTakeValueFromD(b[..], c[..], d[..], i, j);
		lemmaInvSortedTakeValueFromD(b[..], c[..], d[..], i, j);
		j := j + 1;
	}
}

//ATOM
ghost predicate InvSorted(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat){
	i <= |c| && j <= |d| && i + j <= |b| &&
	((i+j > 0 && i < |c|) ==> (b[j + i - 1] <= c[i])) &&
	((i+j > 0 && j < |d|) ==> (b[j + i - 1] <= d[j])) &&
	Sorted(b[..i+j])
}

//ATOM
ghost predicate InvSubSet(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat){
	i <= |c| && j <= |d| && i + j <= |b| &&
	multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
}

//IMPL
lemma LemmaMultysetsEquals (b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
	requires i == |c|;
	requires j == |d|;
	requires i + j == |b|;
	requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
	ensures multiset(b[..]) == multiset(c[..])+multiset(d[..]);
{
	/* code modified by LLM (iteration 4): complete proof of multiset equality */
	assert b[..i+j] == b[..];
	assert c[..i] == c[..];
	assert d[..j] == d[..];
	assert multiset(b[..]) == multiset(c[..]) + multiset(d[..]);
}

//IMPL
lemma lemmaInvSubsetTakeValueFromC (b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
	requires i < |c|;
	requires j <= |d|;
	requires i + j < |b|;
	requires |c| + |d| == |b|;
	requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
	requires b[i+j] == c[i]
	ensures multiset(b[..i+j+1]) == multiset(c[..i+1])+multiset(d[..j])
{
	/* code modified by LLM (iteration 4): detailed proof of multiset property when taking from c */
	assert b[..i+j+1] == b[..i+j] + [b[i+j]];
	assert c[..i+1] == c[..i] + [c[i]];
	assert b[i+j] == c[i];
	
	calc {
		multiset(b[..i+j+1]);
	==	multiset(b[..i+j] + [b[i+j]]);
	==	multiset(b[..i+j]) + multiset([b[i+j]]);
	==	multiset(c[..i]) + multiset(d[..j]) + multiset([c[i]]);
	==	multiset(c[..i]) + multiset([c[i]]) + multiset(d[..j]);
	==	multiset(c[..i] + [c[i]]) + multiset(d[..j]);
	==	multiset(c[..i+1]) + multiset(d[..j]);
	}
}

//IMPL
lemma lemmaInvSubsetTakeValueFromD (b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
	requires i <= |c|;
	requires j < |d|;
	requires i + j < |b|;
	requires |c| + |d| == |b|;
	requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
	requires b[i+j] == d[j]
	ensures multiset(b[..i+j+1]) == multiset(c[..i])+multiset(d[..j+1])
{
	/* code modified by LLM (iteration 4): detailed proof of multiset property when taking from d */
	assert b[..i+j+1] == b[..i+j] + [b[i+j]];
	assert d[..j+1] == d[..j] + [d[j]];
	assert b[i+j] == d[j];
	
	calc {
		multiset(b[..i+j+1]);
	==	multiset(b[..i+j] + [b[i+j]]);
	==	multiset(b[..i+j]) + multiset([b[i+j]]);
	==	multiset(c[..i]) + multiset(d[..j]) + multiset([d[j]]);
	==	multiset(c[..i]) + (multiset(d[..j]) + multiset([d[j]]));
	==	multiset(c[..i]) + multiset(d[..j] + [d[j]]);
	==	multiset(c[..i]) + multiset(d[..j+1]);
	}
}

//IMPL
lemma lemmaInvSortedTakeValueFromC (b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
	requires i < |c|;
	requires j <= |d|;
	requires i + j < |b|;
	requires |c| + |d| == |b|;
	requires Sorted(c[..]) && Sorted(d[..]);
	requires InvSorted(b, c, d, i, j);
	requires b[i+j] == c[i];
	ensures InvSorted(b, c, d, i+1, j);
{
	/* code modified by LLM (iteration 4): complete proof that sorted invariant is maintained when taking from c */
	var b_new := b[..i+j+1];
	
	// Prove Sorted(b_new)
	forall k1, k2 | 0 <= k1 <= k2 < |b_new|
		ensures b_new[k1] <= b_new[k2]
	{
		if k2 < i + j {
			assert b_new[k1] <= b_new[k2]; // from Sorted(b[..i+j])
		} else if k1 < i + j && k2 == i + j {
			assert b_new[k2] == c[i];
			assert b_new[k1] == b[k1];
			if i + j > 0 {
				assert b[i+j-1] <= c[i]; // from InvSorted precondition
			}
		}
	}
	assert Sorted(b_new);
	
	// Prove the invariant conditions
	assert i+1 <= |c| && j <= |d| && (i+1) + j <= |b|;
	
	if (i+1)+j > 0 && i+1 < |c| {
		assert c[i] <= c[i+1]; // from Sorted(c[..])
		assert b[j + (i+1) - 1] == c[i] <= c[i+1];
	}
	
	if (i+1)+j > 0 && j < |d| {
		assert b[j + (i+1) - 1] == c[i];
	}
}

//IMPL
lemma lemmaInvSortedTakeValueFromD (b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
	requires i <= |c|;
	requires j < |d|;
	requires i + j < |b|;
	requires |c| + |d| == |b|;
	requires Sorted(c[..]) && Sorted(d[..]);
	requires InvSorted(b, c, d, i, j);
	requires b[i+j] == d[j];
	ensures InvSorted(b, c, d, i, j+1);
{
	/* code modified by LLM (iteration 4): complete proof that sorted invariant is maintained when taking from d */
	var b_new := b[..i+j+1];
	
	// Prove Sorted(b_new)
	forall k1, k2 | 0 <= k1 <= k2 < |b_new|
		ensures b_new[k1] <= b_new[k2]
	{
		if k2 < i + j {
			assert b_new[k1] <= b_new[k2]; // from Sorted(b[..i+j])
		} else if k1 < i + j && k2 == i + j {
			assert b_new[k2] == d[j];
			assert b_new[k1] == b[k1];
			if i + j > 0 {
				assert b[i+j-1] <= d[j]; // from InvSorted precondition
			}
		}
	}
	assert Sorted(b_new);
	
	// Prove the invariant conditions
	assert i <= |c| && j+1 <= |d| && i + (j+1) <= |b|;
	
	if i+(j+1) > 0 && i < |c| {
		assert b[j+1 + i - 1] == d[j];
	}
	
	if i+(j+1) > 0 && j+1 < |d| {
		assert d[j] <= d[j+1]; // from Sorted(d[..])
		assert b[j+1 + i - 1] == d[j] <= d[j+1];
	}
}

//IMPL
method Main() {
	/* code modified by LLM (iteration 4): fixed array initialization syntax */
	var a := new int[3];
	a[0] := 4; a[1] := 8; a[2] := 6;
	var q0 := a[..];
	a := MergeSort(a);
	print "\nThe sorted version of ", q0, " is ", a[..];

	a := new int[5];
	a[0] := 3; a[1] := 8; a[2] := 5; a[3] := -1; a[4] := 10;
	q0 := a[..];
	a := MergeSort(a);
	print "\nThe sorted version of ", q0, " is ", a[..];
}