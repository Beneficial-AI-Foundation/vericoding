//IMPL 

// Hoare's FIND program [C.A.R. Hoare, "Proof of a program: FIND", CACM 14(1): 39-45, 1971].
// The proof annotations here are not the same as in Hoare's article.

// In Hoare's words:
//  This program operates on an array A[1:N], and a value of f (1 <= f <= N).
//  Its effect is to rearrange the elements of A in such a way that:
//   forall p,q (1 <= p <= f <= q <= N ==> A[p] <= A[f] <= A[q]).
//
// Here, we use 0-based indices, so we would say:
//  This method operates on an array A[0..N], and a value of f (0 <= f < N).
//  Its effect is to rearrange the elements of A in such a way that:
//   forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[f] <= A[q]).

method FIND(A: array<int>, N: int, f: int)
 requires A.Length == N
 requires 0 <= f < N
 modifies A
 ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q]
{
    var i := 0;
    var j := N - 1;
    
    /* code modified by LLM (iteration 3): Track the target value and its current position */
    var target := A[f];
    var target_pos := f;
    
    while i < j
        /* code modified by LLM (iteration 3): Updated invariants to track target value and position correctly */
        invariant 0 <= i <= j < N
        invariant i <= target_pos <= j
        invariant A[target_pos] == target
        invariant forall p :: 0 <= p < i ==> A[p] <= target
        invariant forall q :: j < q < N ==> target <= A[q]
    {
        while i < target_pos && A[i] <= target
            /* code modified by LLM (iteration 3): Use target_pos instead of f */
            invariant 0 <= i <= target_pos
            invariant forall p :: 0 <= p < i ==> A[p] <= target
        {
            i := i + 1;
        }
        
        while j > target_pos && A[j] >= target
            /* code modified by LLM (iteration 3): Use target_pos instead of f */
            invariant target_pos <= j < N
            invariant forall q :: j < q < N ==> target <= A[q]
        {
            j := j - 1;
        }
        
        if i < j {
            /* code modified by LLM (iteration 3): Handle swap and update target position if needed */
            if i == target_pos {
                target_pos := j;
            } else if j == target_pos {
                target_pos := i;
            }
            A[i], A[j] := A[j], A[i];
        }
    }
    
    /* code modified by LLM (iteration 3): Fixed assertion syntax and final positioning logic */
    assert i == j;
    assert i == target_pos;
    assert A[target_pos] == target;
    assert forall p :: 0 <= p < target_pos ==> A[p] <= target;
    assert forall q :: target_pos < q < N ==> target <= A[q];
    
    /* code modified by LLM (iteration 3): Move target to position f if needed while preserving partitioning */
    if target_pos < f {
        // target is to the left of f, need to move it right
        var k := target_pos;
        while k < f
            invariant target_pos <= k <= f
            invariant A[k] == target
            invariant forall p :: 0 <= p < k ==> A[p] <= target
            invariant forall q :: k < q < N ==> target <= A[q]
        {
            A[k], A[k+1] := A[k+1], A[k];
            k := k + 1;
        }
    } else if target_pos > f {
        // target is to the right of f, need to move it left
        var k := target_pos;
        while k > f
            invariant f <= k <= target_pos
            invariant A[k] == target
            invariant forall p :: 0 <= p < k ==> A[p] <= target
            invariant forall q :: k < q < N ==> target <= A[q]
        {
            A[k], A[k-1] := A[k-1], A[k];
            k := k - 1;
        }
    }
}