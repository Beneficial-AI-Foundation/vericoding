/*
Bubble Sort is the simplest sorting algorithm that works by 
repeatedly swapping the adjacent elements if they are in wrong order.
*/

predicate sorted_between(A:array<int>, from:int, to:int)
    reads A
{
    forall i, j :: 0 <= i <= j < A.Length && from <= i <= j <= to ==> A[i] <= A[j]
}

predicate sorted(A:array<int>)
    reads A
{
    sorted_between(A, 0, A.Length-1)
}

/* Explanation:

invariant forall n, m :: 0 <= n <= i <m <N ==> A [n] <= A [m]
     // A is ordered for each pair of elements such that
     // the first element belongs to the left partition of i
     // and the second element belongs to the right partition of i

invariant forall n :: 0 <= n <= j ==> A [n] <= A [j]
     // There is a variable defined by the value that the array takes at position j
     // Therefore, each value that the array takes for all elements from 0 to j
     // They are less than or equal to the value of the variable
*/

// <vc-helpers>
lemma SortedBetweenTransitive(A: array<int>, from: int, mid: int, to: int)
    requires 0 <= from <= mid <= to < A.Length
    requires sorted_between(A, from, mid)
    requires sorted_between(A, mid, to)
    requires mid < to ==> A[mid] <= A[mid+1]
    ensures sorted_between(A, from, to)
{
    // This lemma helps prove that if two adjacent sorted regions are connected properly,
    // the entire region is sorted
}

lemma SwapPreservesMultiset(A: array<int>, i: int, j: int)
    requires 0 <= i < A.Length
    requires 0 <= j < A.Length
    requires i != j
    ensures multiset(A[..][i := A[j]][j := A[i]]) == multiset(A[..])
{
    // This lemma proves that swapping two elements preserves the multiset
}
// </vc-helpers>

// <vc-spec>
method BubbleSort(A:array<int>)
    modifies A
    ensures sorted(A)
    ensures multiset(A[..]) == multiset(old(A[..]))
// </vc-spec>
// <vc-code>
{
    var N := A.Length;
    var i := N - 1;
    
    while i > 0
        invariant -1 <= i < N
        invariant sorted_between(A, i+1, N-1)
        invariant forall n, m :: 0 <= n <= i < m < N ==> A[n] <= A[m]
        invariant multiset(A[..]) == multiset(old(A[..]))
    {
        var j := 0;
        
        while j < i
            invariant 0 <= j <= i
            invariant forall n :: 0 <= n < j ==> A[n] <= A[j]
            invariant sorted_between(A, i+1, N-1)
            invariant forall n, m :: 0 <= n <= i < m < N ==> A[n] <= A[m]
            invariant multiset(A[..]) == multiset(old(A[..]))
        {
            if A[j] > A[j+1] {
                A[j], A[j+1] := A[j+1], A[j];
            }
            j := j + 1;
        }
        
        i := i - 1;
    }
}
// </vc-code>

