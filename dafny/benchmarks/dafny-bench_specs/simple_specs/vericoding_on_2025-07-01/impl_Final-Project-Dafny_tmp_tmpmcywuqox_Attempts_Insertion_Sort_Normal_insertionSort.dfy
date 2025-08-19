//ATOM

predicate sortedA (a: array<int>, i: int)

	requires 0 <= i <= a.Length
	reads a
{
	forall k :: 0 < k < i ==> a[k-1] <= a[k]
}

//ATOM

method lookForMin (a: array<int>, i: int) returns (m: int)

	requires 0 <= i < a.Length
	ensures i <= m < a.Length
	ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{
  m := 0;
  assume i <= m < a.Length;
  assume forall k :: i <= k < a.Length ==> a[k] >= a[m];
  return m;
}

//ATOM

predicate sorted (a: array<int>)

	reads a
{
	sortedA(a, a.Length)
}


// SPEC

method insertionSort (a: array<int>)

	modifies a
	ensures sorted(a)
{
}