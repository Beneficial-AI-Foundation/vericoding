method MergeSort(a: array<int>) returns (b: array<int>)
	ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
{
  /* code modified by LLM (iteration 2): Implemented proper merge sort algorithm */
  if a.Length <= 1 {
    b := new int[a.Length];
    if a.Length == 1 {
      b[0] := a[0];
    }
    return b;
  }
  
  var mid := a.Length / 2;
  var left := new int[mid];
  var right := new int[a.Length - mid];
  
  var i := 0;
  while i < mid 
    invariant 0 <= i <= mid
    modifies left
  {
    left[i] := a[i];
    i := i + 1;
  }
  
  i := 0;
  while i < a.Length - mid
    invariant 0 <= i <= a.Length - mid
    modifies right
  {
    right[i] := a[mid + i];
    i := i + 1;
  }
  
  var sorted_left := MergeSort(left);
  var sorted_right := MergeSort(right);
  
  b := new int[a.Length];
  Merge(b, sorted_left, sorted_right);
}

//ATOM
predicate Sorted(q: seq<int>) {
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

//ATOM
method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c[..]) && Sorted(d[..])
	ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
{
  /* code modified by LLM (iteration 2): Fixed compilation error by removing invalid axiom syntax */
  var i, j, k := 0, 0, 0;
  
  while k < b.Length
    invariant 0 <= i <= c.Length
    invariant 0 <= j <= d.Length  
    invariant 0 <= k <= b.Length
    invariant i + j == k
    invariant Sorted(b[..k])
    invariant multiset(b[..k]) == multiset(c[..i]) + multiset(d[..j])
    invariant i < c.Length && j < d.Length ==> c[i] <= d[j] || d[j] <= c[i]
    modifies b
  {
    if i >= c.Length {
      b[k] := d[j];
      j := j + 1;
    } else if j >= d.Length {
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

//IMPL Main
method Main() {
	/* code modified by LLM (iteration 1): Fixed array initialization to use proper sequence indexing */
	var seq1 := [4, 8, 6];
	var a := new int[3] (i => seq1[i]);
	var q0 := a[..];
	var sorted_a := MergeSort(a);
	print "\nThe sorted version of ", q0, " is ", sorted_a[..];

	/* code modified by LLM (iteration 1): Fixed array initialization to use proper sequence indexing */
	var seq2 := [3, 8, 5, -1, 10];
	a := new int[5] (i => seq2[i]);
	q0 := a[..];
	sorted_a := MergeSort(a);
	print "\nThe sorted version of ", q0, " is ", sorted_a[..];
}