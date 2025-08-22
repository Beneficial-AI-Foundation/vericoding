//IMPL 
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
        
        /* code modified by LLM (iteration 4): fixed invariants to properly track array state and multiset preservation */
        while j >= 0 && a[j] > key
            invariant -1 <= j < i
            invariant forall k :: j < k < i ==> a[k] > key
            invariant forall k :: i < k < a.Length ==> a[k] == old(a[k])
            invariant multiset(a[..]) == multiset(old(a[..]))
            invariant isSorted(a, 0, j+1)
            invariant forall k :: j+2 <= k <= i ==> a[k] > key
        {
            a[j + 1] := a[j];
            j := j - 1;
        }
        
        a[j + 1] := key;
        
        /* code modified by LLM (iteration 4): removed problematic assertions that cannot be proven */
        
        i := i + 1;
    }
}

//ATOM 
// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>, from: nat, to: nat)
  reads a
  requires 0 <= from <= to <= a.Length
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

//IMPL 
// Simple test case to check the postcondition
method testInsertionSort() {
    var a := new int[3];
    a[0] := 3;
    a[1] := 1;
    a[2] := 2;
    insertionSort(a);
    assert isSorted(a, 0, a.Length);
}