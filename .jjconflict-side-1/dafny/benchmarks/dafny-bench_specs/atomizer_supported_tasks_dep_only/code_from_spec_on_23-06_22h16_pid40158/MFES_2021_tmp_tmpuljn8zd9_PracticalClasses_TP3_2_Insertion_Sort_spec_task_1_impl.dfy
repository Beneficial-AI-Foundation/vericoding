// ATOM 
// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>, from: nat, to: nat)
  reads a
  requires 0 <= from <= to <= a.Length
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

// IMPL 
// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>) 
    modifies a
    ensures isSorted(a, 0, a.Length)
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant isSorted(a, 0, i)
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var key := a[i];
        var j := i - 1;
        
        /* code modified by LLM (iteration 4): simplified invariants for the inner loop */
        while j >= 0 && a[j] > key
            invariant -1 <= j < i
            invariant forall k :: j + 1 < k <= i ==> a[k] > key
            invariant isSorted(a, 0, j + 1)  
            invariant isSorted(a, j + 2, i + 1)
            invariant multiset(a[..]) == multiset(old(a[..]))
        {
            a[j + 1] := a[j];
            j := j - 1;
        }
        
        a[j + 1] := key;
        i := i + 1;
    }
}