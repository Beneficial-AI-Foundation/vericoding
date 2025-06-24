//ATOM_PLACEHOLDER_sorted

//ATOM_PLACEHOLDER_sortedA

// SPEC 

method lookForMin (a: array<int>, i: int) returns (m: int)

	requires 0 <= i < a.Length
	ensures i <= m < a.Length
	ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{
}


//ATOM_PLACEHOLDER_insertionSort

