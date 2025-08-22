//ATOM

predicate sorted' (a: array<int>, i: int)
	requires a != null
	requires 0 <= i <= a.Length
	reads a
{
	forall k :: 0 < k < i ==> a[k-1] <= a[k]
}


// SPEC


// Selection sort on arrays

method SelectionSort(a: array<int>) 
 modifies a
 ensures sorted(a)
 //ensures multiset(old(a[..])) == multiset(a[..])
{
}
