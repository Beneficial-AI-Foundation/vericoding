//IMPL FIND
method FIND(A: array<int>, N: int, f: int)
 requires A.Length == N
 requires 0 <= f < N
 modifies A
 ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q]
{
    /* code modified by LLM (iteration 1): Simple selection sort approach for correctness */
    
    // First, find the (f+1)-th smallest element and put it at position f
    var k := 0;
    while k <= f
        invariant 0 <= k <= f + 1
        invariant forall i, j :: 0 <= i < k <= j < N ==> A[i] <= A[j]
        decreases f - k + 1
    {
        // Find minimum element in A[k..N-1] and swap it to position k
        var minPos := k;
        var j := k + 1;
        
        while j < N
            invariant k <= minPos < N
            invariant k + 1 <= j <= N
            invariant forall m :: k <= m < j ==> A[minPos] <= A[m]
            decreases N - j
        {
            if A[j] < A[minPos] {
                minPos := j;
            }
            j := j + 1;
        }
        
        // Swap minimum element to position k
        if minPos != k {
            A[k], A[minPos] := A[minPos], A[k];
        }
        
        k := k + 1;
    }
    
    /* code modified by LLM (iteration 1): Now ensure elements after f are >= A[f] */
    var pivot := A[f];
    var i := f + 1;
    
    while i < N
        invariant f + 1 <= i <= N
        invariant forall p :: 0 <= p <= f ==> A[p] <= pivot
        invariant forall q :: f < q < i ==> A[q] >= pivot
        decreases N - i
    {
        if A[i] < pivot {
            // Find a position >= f+1 where we can place A[i]
            var pos := f + 1;
            while pos < i && A[pos] < pivot
                invariant f + 1 <= pos <= i
                decreases i - pos
            {
                pos := pos + 1;
            }
            
            if pos < i {
                A[i], A[pos] := A[pos], A[i];
            } else {
                // Move A[i] to the left part and shift elements
                var temp := A[i];
                var j := i;
                while j > f + 1
                    invariant f + 1 <= j <= i
                    decreases j
                {
                    A[j] := A[j-1];
                    j := j - 1;
                }
                A[f + 1] := temp;
                
                // Update pivot if necessary
                if temp > pivot {
                    pivot := temp;
                }
            }
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): Final verification helper */
    // The first part is already sorted, and we've ensured the second part
    // has elements >= pivot, so the postcondition should hold
}