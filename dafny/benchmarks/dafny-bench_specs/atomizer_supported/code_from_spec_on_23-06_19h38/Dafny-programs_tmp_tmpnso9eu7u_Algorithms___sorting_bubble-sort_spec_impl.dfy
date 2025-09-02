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
        /* code modified by LLM (iteration 1): Fixed invariant to track sorted suffix starting from correct position */
        invariant i > 0 ==> sorted_between(A, n - i, n - 1)
        /* code modified by LLM (iteration 1): Added invariant to ensure elements before sorted suffix are <= elements in sorted suffix */
        invariant i > 0 ==> forall k, l :: 0 <= k < n - i && n - i <= l < n ==> A[k] <= A[l]
    {
        var j := 0;
        
        while j < n - i - 1
            invariant 0 <= j <= n - i - 1
            invariant multiset(A[..]) == multiset(old(A[..]))
            invariant i > 0 ==> sorted_between(A, n - i, n - 1)
            invariant i > 0 ==> forall k, l :: 0 <= k < n - i && n - i <= l < n ==> A[k] <= A[l]
            /* code modified by LLM (iteration 1): Added invariant to track maximum element bubbling to the right */
            invariant forall k :: 0 <= k <= j ==> A[k] <= A[j]
        {
            if A[j] > A[j + 1] {
                var temp := A[j];
                A[j] := A[j + 1];
                A[j + 1] := temp;
            }
            j := j + 1;
        }
        
        /* code modified by LLM (iteration 1): Added assertion to help prove loop invariant maintenance */
        assert forall k :: 0 <= k < n - i - 1 ==> A[k] <= A[n - i - 1];
        
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): Added final assertion to establish postcondition */
    assert i == n - 1;
    assert sorted_between(A, 1, n - 1);
    assert n > 1 ==> forall k :: 0 <= k < 1 && 1 <= k < n ==> A[0] <= A[k];
}


// IMPL Main

method Main() {
}