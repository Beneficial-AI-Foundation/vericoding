//ATOM
predicate sorted' (a: array<int>, i: int)
	/* code modified by LLM (iteration 1): removed redundant null check since array<int> is non-null by default */
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
    if a.Length <= 1 {
        return;
    }
    
    var i := 0;
    while i < a.Length - 1
        invariant 0 <= i <= a.Length - 1
        invariant forall k, j :: 0 <= k < i <= j < a.Length ==> a[k] <= a[j]
        invariant forall k :: 0 < k < i ==> a[k-1] <= a[k]
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
        
        // Swap elements at positions i and minIndex
        var temp := a[i];
        a[i] := a[minIndex];
        a[minIndex] := temp;
        
        i := i + 1;
    }
}

predicate sorted(a: array<int>)
    /* code modified by LLM (iteration 1): removed redundant null check since array<int> is non-null by default */
    reads a
{
    forall k :: 0 < k < a.Length ==> a[k-1] <= a[k]
}