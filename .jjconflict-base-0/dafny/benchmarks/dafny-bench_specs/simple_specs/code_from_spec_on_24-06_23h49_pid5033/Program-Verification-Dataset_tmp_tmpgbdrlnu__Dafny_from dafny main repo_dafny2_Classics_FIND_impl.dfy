//IMPL FIND
method FIND(A: array<int>, N: int, f: int)
 requires A.Length == N
 requires 0 <= f < N
 modifies A
 ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q]
{
    /* code modified by LLM (iteration 3): Simple selection algorithm to ensure partition property */
    var i := 0;
    
    // For each position from 0 to f, find the minimum element from position i onwards
    // and place it at position i
    while i <= f
        invariant 0 <= i <= f + 1
        invariant forall p,q :: 0 <= p < i && i <= q < N ==> A[p] <= A[q]
        invariant forall p,q :: 0 <= p < q < i ==> A[p] <= A[q]
        decreases f + 1 - i
    {
        // Find minimum element from position i to N-1
        var minPos := i;
        var j := i + 1;
        
        while j < N
            invariant i <= minPos < N
            invariant i <= j <= N
            invariant forall k :: i <= k < j ==> A[minPos] <= A[k]
            decreases N - j
        {
            if A[j] < A[minPos] {
                minPos := j;
            }
            j := j + 1;
        }
        
        // Swap minimum element to position i
        if minPos != i {
            A[i], A[minPos] := A[minPos], A[i];
        }
        
        i := i + 1;
    }
}