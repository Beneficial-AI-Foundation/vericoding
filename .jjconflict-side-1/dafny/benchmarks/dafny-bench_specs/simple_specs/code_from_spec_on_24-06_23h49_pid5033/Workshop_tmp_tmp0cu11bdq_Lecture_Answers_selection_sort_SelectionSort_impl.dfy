//ATOM

predicate sorted' (a: array<int>, i: int)
	requires a != null
	requires 0 <= i <= a.Length
	reads a
{
	forall k :: 0 < k < i ==> a[k-1] <= a[k]
}

//IMPL Selection sort on arrays

method SelectionSort(a: array<int>) 
 modifies a
 ensures sorted(a)
 //ensures multiset(old(a[..])) == multiset(a[..])
{
	if a == null || a.Length <= 1 {
		return;
	}
	
	var i := 0;
	while i < a.Length - 1
		invariant 0 <= i <= a.Length
		invariant sorted'(a, i)
		invariant forall j, k :: 0 <= j < i && i <= k < a.Length ==> a[j] <= a[k]
	{
		var minIndex := i;
		var j := i + 1;
		
		while j < a.Length
			invariant i <= minIndex < a.Length
			invariant i + 1 <= j <= a.Length
			invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
		{
			if a[j] < a[minIndex] {
				minIndex := j;
			}
			j := j + 1;
		}
		
		if minIndex != i {
			var temp := a[i];
			a[i] := a[minIndex];
			a[minIndex] := temp;
		}
		
		i := i + 1;
	}
}

predicate sorted(a: array<int>)
	requires a != null
	reads a
{
	forall i :: 0 < i < a.Length ==> a[i-1] <= a[i]
}