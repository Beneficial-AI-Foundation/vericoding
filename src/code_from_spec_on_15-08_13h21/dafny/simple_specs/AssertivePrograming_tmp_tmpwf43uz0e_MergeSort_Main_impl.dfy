//IMPL MergeSort
method MergeSort(a: array<int>) returns (b: array<int>)
	ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
	decreases a.Length
{
  /* code modified by LLM (iteration 4): Added multiset preservation proofs */
  b := new int[a.Length];
  
  if a.Length <= 1 {
    if a.Length == 1 {
      b[0] := a[0];
    }
    return b;
  }
  
  var mid := a.Length / 2;
  var left := new int[mid];
  var right := new int[a.Length - mid];
  
  // Copy elements to left and right arrays
  var i := 0;
  while i < mid
    invariant 0 <= i <= mid
    invariant forall j :: 0 <= j < i ==> left[j] == a[j]
    invariant multiset(left[..i]) == multiset(a[..i])
  {
    left[i] := a[i];
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 4): Added multiset preservation assertion */
  assert multiset(left[..]) == multiset(a[..mid]);
  
  i := 0;
  while i < a.Length - mid
    invariant 0 <= i <= a.Length - mid
    invariant forall j :: 0 <= j < i ==> right[j] == a[mid + j]
    invariant multiset(right[..i]) == multiset(a[mid..mid+i])
  {
    right[i] := a[mid + i];
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 4): Added multiset preservation assertions */
  assert multiset(right[..]) == multiset(a[mid..]);
  assert multiset(a[..]) == multiset(a[..mid]) + multiset(a[mid..]);
  assert multiset(left[..]) + multiset(right[..]) == multiset(a[..]);
  
  // Recursively sort left and right
  var sortedLeft := MergeSort(left);
  var sortedRight := MergeSort(right);
  
  /* code modified by LLM (iteration 4): Added assertions to connect multisets */
  assert multiset(sortedLeft[..]) == multiset(left[..]);
  assert multiset(sortedRight[..]) == multiset(right[..]);
  assert multiset(sortedLeft[..]) + multiset(sortedRight[..]) == multiset(a[..]);
  
  // Merge the sorted arrays
  Merge(b, sortedLeft, sortedRight);
  
  /* code modified by LLM (iteration 4): Added final multiset assertion */
  assert multiset(b[..]) == multiset(sortedLeft[..]) + multiset(sortedRight[..]);
  assert multiset(b[..]) == multiset(a[..]);
  
  return b;
}


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
  /* code modified by LLM (iteration 4): Enhanced loop invariants for multiset preservation */
  var i, j, k := 0, 0, 0;
  
  while i < c.Length && j < d.Length
    invariant 0 <= i <= c.Length && 0 <= j <= d.Length && k == i + j
    invariant Sorted(b[..k])
    invariant multiset(b[..k]) == multiset(c[..i]) + multiset(d[..j])
    invariant i < c.Length ==> forall x :: 0 <= x < k ==> b[x] <= c[i]
    invariant j < d.Length ==> forall x :: 0 <= x < k ==> b[x] <= d[j]
  {
    if c[i] <= d[j] {
      b[k] := c[i];
      i := i + 1;
    } else {
      b[k] := d[j];
      j := j + 1;
    }
    k := k + 1;
  }
  
  while i < c.Length
    invariant 0 <= i <= c.Length && j == d.Length && k == i + j
    invariant multiset(b[..k]) == multiset(c[..i]) + multiset(d[..j])
    invariant Sorted(b[..k])
    invariant i < c.Length ==> (k == 0 || b[k-1] <= c[i])
  {
    b[k] := c[i];
    i := i + 1;
    k := k + 1;
  }
  
  while j < d.Length
    invariant i == c.Length && 0 <= j <= d.Length && k == i + j
    invariant multiset(b[..k]) == multiset(c[..i]) + multiset(d[..j])
    invariant Sorted(b[..k])
    invariant j < d.Length ==> (k == 0 || b[k-1] <= d[j])
  {
    b[k] := d[j];
    j := j + 1;
    k := k + 1;
  }
  
  /* code modified by LLM (iteration 4): Final assertion to help verification */
  assert k == b.Length;
  assert multiset(b[..]) == multiset(c[..]) + multiset(d[..]);
}


//IMPL Main
method Main() {
	/* code modified by LLM (iteration 2): Fixed array initialization syntax */
	var a := new int[3];
	a[0], a[1], a[2] := 4, 8, 6;
	var q0 := a[..];
	a := MergeSort(a);
	print "\nThe sorted version of ", q0, " is ", a[..];

	a := new int[5];
	a[0], a[1], a[2], a[3], a[4] := 3, 8, 5, -1, 10;
	q0 := a[..];
	a := MergeSort(a);
	print "\nThe sorted version of ", q0, " is ", a[..];
	//assert a[..] == [-1, 3, 5, 8, 10];
}