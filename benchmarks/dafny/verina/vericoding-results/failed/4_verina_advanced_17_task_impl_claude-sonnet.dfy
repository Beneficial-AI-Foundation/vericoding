// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified lemma for multiset preservation after element insertion */
lemma InsertionPreservesMultiset(a: array<int>, pos: int, val: int)
    requires 0 <= pos < a.Length
    modifies a
    ensures multiset(a[..]) == multiset(old(a[..pos]) + [val] + old(a[pos..]))
{
}

lemma ArrayCopyPreservesMultiset(source: array<int>, dest: array<int>)
    requires source.Length == dest.Length
    requires forall k :: 0 <= k < source.Length ==> dest[k] == source[k]
    ensures multiset(dest[..]) == multiset(source[..])
{
}
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
{
    /* code modified by LLM (iteration 5): simplified implementation with proper multiset tracking */
    result := new int[l.Length];
    
    if l.Length == 0 {
        return;
    }
    
    // Copy all elements first
    var i := 0;
    while i < l.Length
        invariant 0 <= i <= l.Length
        invariant result.Length == l.Length
        invariant forall k :: 0 <= k < i ==> result[k] == l[k]
    {
        result[i] := l[i];
        i := i + 1;
    }
    
    // Now result is a copy of l, so multiset(result[..]) == multiset(l[..])
    
    // Insertion sort
    i := 1;
    while i < result.Length
        invariant 1 <= i <= result.Length
        invariant result.Length == l.Length
        invariant multiset(result[..]) == multiset(l[..])
        invariant forall x, y :: 0 <= x < y < i ==> result[x] <= result[y]
    {
        var key := result[i];
        var j := i - 1;
        
        // Shift elements to make space for key
        while j >= 0 && result[j] > key
            invariant -1 <= j < i
            invariant forall x :: j + 1 < x <= i ==> result[x] > key
            invariant forall x :: i + 1 <= x < result.Length ==> result[x] == old(result[x])
            invariant forall x, y :: 0 <= x < y <= j ==> result[x] <= result[y]
            invariant multiset(result[..]) == multiset(l[..])
            invariant result[i] == key
        {
            result[j + 1] := result[j];
            j := j - 1;
        }
        
        result[j + 1] := key;
        i := i + 1;
    }
}
// </vc-code>
