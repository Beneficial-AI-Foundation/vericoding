// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added multiset preservation lemma */
lemma multiset_swap_preserves_multiset(a: array<int>, i: int, j: int)
    requires 0 <= i < a.Length && 0 <= j < a.Length
    modifies a
    ensures multiset(old(a[..])) == multiset(a[..])
{
    // Dafny can prove this automatically
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
    /* code modified by LLM (iteration 5): fixed invariant propagation with explicit assertions */
    result := new int[l.Length];
    if l.Length == 0 {
        return;
    }
    
    var i := 0;
    while i < l.Length
        invariant 0 <= i <= l.Length
        invariant result.Length == l.Length
        invariant multiset(result[..i]) == multiset(l[..i])
        invariant forall x, y :: 0 <= x < y < i ==> result[x] <= result[y]
    {
        result[i] := l[i];
        
        var j := i;
        while j > 0 && result[j] < result[j-1]
            invariant 0 <= j <= i
            invariant result.Length == l.Length
            invariant multiset(result[..i+1]) == multiset(l[..i+1])
            invariant forall x, y :: 0 <= x < y < j ==> result[x] <= result[y]
            invariant forall x, y :: j < x < y <= i ==> result[x] <= result[y]
            invariant j < i ==> result[j] <= result[j+1]
        {
            var temp := result[j];
            result[j] := result[j-1];
            result[j-1] := temp;
            
            // Help Dafny see that the partial sortedness is maintained
            assert forall x, y :: j-1 < x < y <= i ==> result[x] <= result[y];
            
            j := j - 1;
        }
        
        i := i + 1;
    }
}
// </vc-code>
