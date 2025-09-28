// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate sorted(s: seq<int>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
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
    result := new int[l.Length];
    var i: int := 0;
    while i < l.Length 
        invariant 0 <= i <= l.Length
        invariant sorted(result[..i])
        invariant multiset(result[..i]) == multiset(l[..i])
    {
        var key := l[i];
        var j : int := i;

        ghost var old_result_i := result[..i];

        while j > 0 && result[j-1] > key
            invariant 0 <= j <= i
            invariant sorted(result[..j-1])
            invariant forall k :: j <= k < i ==> result[k] > key
            invariant multiset(result[..i]) == multiset(old_result_i) // Permutation of the slice being modified
        {
            result[j] := result[j-1];
            j := j - 1;
        }
        result[j] := key;

        assert multiset(result[..i+1]) == multiset(old_result_i) + multiset{key};
        assert multiset(result[..i+1]) == multiset(l[..i+1]);
        assert sorted(result[..i+1]);
        
        i := i + 1;
    }
}
// </vc-code>
