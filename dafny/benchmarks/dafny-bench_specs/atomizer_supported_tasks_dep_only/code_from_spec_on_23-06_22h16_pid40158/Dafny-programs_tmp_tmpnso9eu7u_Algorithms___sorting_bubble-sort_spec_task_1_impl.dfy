/*
Bubble Sort is the simplest sorting algorithm that works by 
repeatedly swapping the adjacent elements if they are in wrong order.
*/

// ATOM 

predicate sorted_between(A:array<int>, from:int, to:int)
    reads A
{
    forall i, j :: 0 <= i <= j < A.Length && from <= i <= j <= to ==> A[i] <= A[j]
}


// ATOM 

predicate sorted(A:array<int>)
    reads A
{
    sorted_between(A, 0, A.Length-1)
}


// IMPL BubbleSort

method BubbleSort(A:array<int>)
    modifies A
    ensures sorted(A)
    ensures multiset(A[..]) == multiset(old(A[..]))
{
    if A.Length <= 1 {
        return;
    }
    
    var n := A.Length;
    var i := 0;
    
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant multiset(A[..]) == multiset(old(A[..]))
        /* code modified by LLM (iteration 4): fixed invariant to properly capture that the last i elements are in their final sorted positions */
        invariant sorted_between(A, n - i, n - 1)
        /* code modified by LLM (iteration 4): added invariant that all elements in the unsorted part are <= all elements in the sorted part */
        invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> A[k] <= A[l]
    {
        var j := 0;
        
        while j < n - i - 1
            invariant 0 <= j <= n - i - 1
            invariant multiset(A[..]) == multiset(old(A[..]))
            invariant sorted_between(A, n - i, n - 1)
            invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> A[k] <= A[l]
            /* code modified by LLM (iteration 4): corrected invariant to track that the largest element in [0..j+1] is at position j+1 */
            invariant forall k :: 0 <= k <= j ==> A[k] <= A[j + 1]
        {
            if A[j] > A[j + 1] {
                var temp := A[j];
                A[j] := A[j + 1];
                A[j + 1] := temp;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): added proof that the array is fully sorted */
    assert i == n - 1;
    assert sorted_between(A, 1, n - 1);
    assert forall k :: 0 <= k < 1 ==> forall l :: 1 <= l < n ==> A[k] <= A[l];
    
    /* code modified by LLM (iteration 4): prove transitivity to establish full sorting */
    forall x, y | 0 <= x <= y < n
        ensures A[x] <= A[y]
    {
        if x == 0 && y >= 1 {
            assert A[x] <= A[y]; // from partition property
        } else if x >= 1 && y >= 1 {
            assert A[x] <= A[y]; // from sorted_between(A, 1, n-1)
        } else if x == 0 && y == 0 {
            assert A[x] <= A[y]; // trivial
        }
    }
}