//ATOM

method MergeSort(a: array<int>) returns (b: array<int>)
	ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
{
  /* code modified by LLM (iteration 2): Added proper verification annotations and multiset reasoning */
  if a.Length <= 1 {
    b := new int[a.Length];
    var i := 0;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> b[k] == a[k]
    {
      b[i] := a[i];
      i := i + 1;
    }
    /* code modified by LLM (iteration 2): Added assertions to help verification */
    assert b[..] == a[..];
    assert multiset(b[..]) == multiset(a[..]);
    return b;
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
  
  /* code modified by LLM (iteration 2): Added multiset preservation assertions */
  assert left[..] == a[..mid];
  assert right[..] == a[mid..];
  assert multiset(left[..]) + multiset(right[..]) == multiset(a[..]);
  
  var sortedLeft := MergeSort(left);
  var sortedRight := MergeSort(right);
  
  /* code modified by LLM (iteration 2): Added assertions about recursive call results */
  assert Sorted(sortedLeft[..]) && multiset(sortedLeft[..]) == multiset(left[..]);
  assert Sorted(sortedRight[..]) && multiset(sortedRight[..]) == multiset(right[..]);
  assert multiset(sortedLeft[..]) + multiset(sortedRight[..]) == multiset(a[..]);
  
  b := new int[a.Length];
  /* code modified by LLM (iteration 2): Added assertion before merge to establish preconditions */
  assert b.Length == sortedLeft.Length + sortedRight.Length;
  Merge(b, sortedLeft, sortedRight);
  
  /* code modified by LLM (iteration 2): Added final assertion to help verification */
  assert multiset(b[..]) == multiset(sortedLeft[..]) + multiset(sortedRight[..]);
  assert multiset(b[..]) == multiset(a[..]);
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
  assume Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..]);
}


// SPEC

method Main() {
	/* code modified by LLM (iteration 4): Fixed array initialization syntax to use proper Dafny syntax */
	var a := new int[3];
	a[0] := 4; a[1] := 8; a[2] := 6;
	var q0 := a[..];
	a := MergeSort(a);
	print "\nThe sorted version of ", q0, " is ", a[..];

	/* code modified by LLM (iteration 4): Fixed array initialization syntax to use proper Dafny syntax */
	a := new int[5];
	a[0] := 3; a[1] := 8; a[2] := 5; a[3] := -1; a[4] := 10;
	q0 := a[..];
	a := MergeSort(a);
	print "\nThe sorted version of ", q0, " is ", a[..];
	//assert a[..] == [-1, 3, 5, 8, 10];
}