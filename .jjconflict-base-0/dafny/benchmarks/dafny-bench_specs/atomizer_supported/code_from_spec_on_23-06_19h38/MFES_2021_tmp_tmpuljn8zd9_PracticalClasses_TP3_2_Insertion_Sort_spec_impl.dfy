// Sorts array 'a' using the insertion sort algorithm.
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
        
        /* code modified by LLM (iteration 4): capture array state before inner loop */
        ghost var arrayBeforeShift := a[..];
        
        while j >= 0 && a[j] > key
            invariant -1 <= j < i
            invariant multiset(a[..]) == multiset(arrayBeforeShift)
            invariant isSorted(a, 0, j + 1)
            invariant forall k :: j + 2 <= k <= i ==> a[k] > key
            invariant forall k :: 0 <= k <= j ==> a[k] == arrayBeforeShift[k]
            invariant forall k :: j + 2 <= k <= i ==> a[k] == arrayBeforeShift[k-1]
            invariant arrayBeforeShift[i] == key
        {
            a[j + 1] := a[j];
            j := j - 1;
        }
        
        a[j + 1] := key;
        
        /* code modified by LLM (iteration 4): prove sortedness with helper assertions */
        assert forall k :: 0 <= k <= j ==> a[k] <= key;
        assert forall k :: j + 2 <= k <= i ==> a[k] >= key;
        assert a[j + 1] == key;
        assert isSorted(a, 0, j + 1);
        assert isSorted(a, j + 1, i + 1);
        assert isSorted(a, 0, i + 1);
        
        i := i + 1;
    }
}

// Checks if array 'a' is sorted.
//ATOM 

// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>, from: nat, to: nat)
  reads a
  requires 0 <= from <= to <= a.Length
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

// Simple test case to check the postcondition
//IMPL 

// Simple test case to check the postcondition
method testInsertionSort() {
    var a := new int[3];
    a[0] := 3;
    a[1] := 1; 
    a[2] := 2;
    
    var oldContents := multiset(a[..]);
    insertionSort(a);
    
    assert isSorted(a, 0, a.Length);
    assert multiset(a[..]) == oldContents;
}