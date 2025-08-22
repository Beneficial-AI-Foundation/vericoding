// Noa Leron 207131871
// Tsuri Farhana 315016907

//ATOM 
predicate Sorted(q: seq<int>) {
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
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
	
	/* code modified by LLM (iteration 1): Added multiset reasoning for array copying */
	assert left[..] == a[0..mid];
	assert right[..] == a[mid..a.Length];
	assert multiset(left[..]) == multiset(a[0..mid]);
	assert multiset(right[..]) == multiset(a[mid..a.Length]);
	assert multiset(a[0..mid]) + multiset(a[mid..a.Length]) == multiset(a[..]);
	
	var sortedLeft := MergeSort(left);
	var sortedRight := MergeSort(right);
	
	b := new int[a.Length];
	
	/* code modified by LLM (iteration 1): Added assertions for merge preconditions */
	assert sortedLeft.Length == left.Length == mid;
	assert sortedRight.Length == right.Length == a.Length - mid;
	assert b.Length == sortedLeft.Length + sortedRight.Length;
	assert multiset(sortedLeft[..]) == multiset(left[..]);
	assert multiset(sortedRight[..]) == multiset(right[..]);
	
	Merge(b, sortedLeft, sortedRight);
	
	/* code modified by LLM (iteration 1): Added multiset equality chain */
	assert multiset(b[..]) == multiset(sortedLeft[..]) + multiset(sortedRight[..]);
	assert multiset(sortedLeft[..]) + multiset(sortedRight[..]) == multiset(left[..]) + multiset(right[..]);
	assert multiset(left[..]) + multiset(right[..]) == multiset(a[0..mid]) + multiset(a[mid..a.Length]);
	assert multiset(a[0..mid]) + multiset(a[mid..a.Length]) == multiset(a[..]);
}

//ATOM 
ghost predicate Inv(a: seq<int>, a1: seq<int>, a2: seq<int>, i: nat, mid: nat){
    (i <= |a1|) && (i <= |a2|) && (i+mid <= |a|) &&
    (a1[..i] == a[..i]) && (a2[..i] == a[mid..(i+mid)])
}

//IMPL Merge
method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c[..]) && Sorted(d[..])
	ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
{
	var i, j := 0, 0;
	
	while i + j < b.Length
		invariant 0 <= i <= c.Length
		invariant 0 <= j <= d.Length
		invariant i + j <= b.Length
		invariant InvSubSet(b[..], c[..], d[..], i, j)
		invariant InvSorted(b[..], c[..], d[..], i, j)
		decreases b.Length - (i + j)
	{
		/* code modified by LLM (iteration 1): Fixed merge logic and added proper state updates */
		if i == c.Length {
			b[i + j] := d[j];
			lemmaInvSubsetTakeValueFromD(b[..], c[..], d[..], i, j);
			j := j + 1;
		} else if j == d.Length {
			b[i + j] := c[i];
			lemmaInvSubsetTakeValueFromC(b[..], c[..], d[..], i, j);
			i := i + 1;
		} else if d[j] < c[i] {
			b[i + j] := d[j];
			lemmaInvSubsetTakeValueFromD(b[..], c[..], d[..], i, j);
			j := j + 1;
		} else {
			b[i + j] := c[i];
			lemmaInvSubsetTakeValueFromC(b[..], c[..], d[..], i, j);
			i := i + 1;
		}
	}
	
	/* code modified by LLM (iteration 1): Final verification that all elements are processed */
	assert i + j == b.Length;
	assert i == c.Length && j == d.Length;
	
	LemmaMultysetsEquals(b[..], c[..], d[..], i, j);
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
		//decreases ensures
		ensures 0 <= c.Length - i < c.Length - i0 || (c.Length - i == c.Length - i0 && 0 <= d.Length - j < d.Length - j0)
		{

			i,j := i0,j0;
				
				if(i == c.Length || (j< d.Length && d[j] < c[i])){
					// in this case we take the next value from d
				b[i+j] := d[j];
				lemmaInvSubsetTakeValueFromD(b[..],c[..],d[..],i,j);

				j := j + 1;
			}
			else{
					// in this case we take the next value from c
				
				b[i+j] := c[i];

				lemmaInvSubsetTakeValueFromC(b[..],c[..],d[..],i,j);
				i := i + 1;
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

method Main() {
}