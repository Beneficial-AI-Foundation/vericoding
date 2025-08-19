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


//IMPL insertionSort

method insertionSort (a: array<int>)

	modifies a
	ensures sorted(a)
{
	if a.Length <= 1 {
		return;
	}
	
	var i := 0;
	while i < a.Length
		invariant 0 <= i <= a.Length
		invariant sortedA(a, i)
		invariant forall j, k :: 0 <= j < i && i <= k < a.Length ==> a[j] <= a[k]
	{
		var minIndex := lookForMin(a, i);
		
		// Swap a[i] and a[minIndex]
		var temp := a[i];
		a[i] := a[minIndex];
		a[minIndex] := temp;
		
		i := i + 1;
	}
}