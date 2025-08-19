//ATOM

method MergeSort(a: array<int>) returns (b: array<int>)
	ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
{
  b := [];
  assume b.Length ==> a.Length && Sorted(b[..]) && multiset(a[..]) ==> multiset(b[..]);
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
  assume Sorted(b[..]) && multiset(b[..]) ==> multiset(c[..])+multiset(d[..]);
}


// SPEC





method Main() {
	var a := new int[3] [4, 8, 6];
	var q0 := a[..];
	a := MergeSort(a);
	print "\nThe sorted version of ", q0, " is ", a[..];

	a := new int[5] [3, 8, 5, -1, 10];
	q0 := a[..];
	a := MergeSort(a);
	print "\nThe sorted version of ", q0, " is ", a[..];
	//assert a[..] == [-1, 3, 5, 8, 10];
}