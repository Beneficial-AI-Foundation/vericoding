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
    
    /* code modified by LLM (iteration 4): Fixed outer loop invariants with correct bounds and reasoning */
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant multiset(A[..]) == multiset(old(A[..]))
        invariant sorted_between(A, n - i, n - 1)
        invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> A[k] <= A[l]
    {
        var j := 0;
        
        /* code modified by LLM (iteration 4): Fixed inner loop invariants to properly track maximum element bubbling */
        while j < n - 1 - i
            invariant 0 <= j <= n - 1 - i
            invariant multiset(A[..]) == multiset(old(A[..]))
            invariant sorted_between(A, n - i, n - 1)
            invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> A[k] <= A[l]
            invariant forall k :: 0 <= k <= j ==> A[k] <= A[j]
        {
            if A[j] > A[j + 1] {
                /* code modified by LLM (iteration 4): Added assertion to help with verification */
                assert A[j] > A[j + 1];
                var temp := A[j];
                A[j] := A[j + 1];
                A[j + 1] := temp;
                /* code modified by LLM (iteration 4): Added assertion after swap */
                assert A[j] <= A[j + 1];
            }
            j := j + 1;
        }
        
        /* code modified by LLM (iteration 4): Added assertion to establish that maximum is at position n-1-i */
        assert forall k :: 0 <= k < n - 1 - i ==> A[k] <= A[n - 1 - i];
        
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Added final assertion to help prove the postcondition */
    assert sorted_between(A, 1, n - 1);
    assert n >= 2 ==> sorted_between(A, 0, n - 1);
}


// IMPL Main

method Main() {
}