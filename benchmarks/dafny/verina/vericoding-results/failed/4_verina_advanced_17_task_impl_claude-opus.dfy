// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method insertion_sort(l: array<int>) returns (result: array<int>)
    ensures
        /* The result is sorted in non-decreasing order */
        forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]
    ensures
        /* The result is a permutation of the input */
        result.Length == l.Length && multiset(result[..]) == multiset(l[..])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed insertion sort with complete invariants for permutation preservation */
{
    result := new int[l.Length];
    
    // Copy array first
    var idx := 0;
    while idx < l.Length
        invariant 0 <= idx <= l.Length
        invariant result.Length == l.Length
        invariant forall k :: 0 <= k < idx ==> result[k] == l[k]
        invariant forall k :: idx <= k < l.Length ==> result[k] == old(result[k])
        invariant multiset(result[..idx]) + multiset(result[idx..]) == multiset(l[..idx]) + multiset(old(result[idx..]))
    {
        result[idx] := l[idx];
        idx := idx + 1;
    }
    
    // Now sort using insertion sort
    var i := 1;
    while i < result.Length
        invariant 1 <= i <= result.Length
        invariant result.Length == l.Length
        invariant multiset(result[..]) == multiset(l[..])
        invariant forall j, k :: 0 <= j < k < i ==> result[j] <= result[k]
    {
        var key := result[i];
        var j := i - 1;
        
        // Save the multiset before modifications
        ghost var oldResult := result[..];
        
        while j >= 0 && result[j] > key
            invariant -1 <= j < i
            invariant result.Length == l.Length
            invariant i < result.Length
            invariant forall m :: j < m <= i && m < result.Length ==> if m == i then result[m] == oldResult[i] else result[m] >= key
            invariant forall p, q :: 0 <= p < q <= j ==> result[p] <= result[q]
            invariant j + 1 < result.Length
            invariant multiset(result[..j+1]) + multiset([key]) + multiset(result[j+2..i]) + multiset(result[i+1..]) == multiset(oldResult)
            invariant forall m :: 0 <= m <= j ==> result[m] == oldResult[m]
            invariant forall m :: j + 2 <= m < i ==> result[m] == oldResult[m-1]
            invariant result[i] == oldResult[i]
            invariant forall m :: i < m < result.Length ==> result[m] == oldResult[m]
        {
            result[j + 1] := result[j];
            j := j - 1;
        }
        
        result[j + 1] := key;
        i := i + 1;
    }
}
// </vc-code>
