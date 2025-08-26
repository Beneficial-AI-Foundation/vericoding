predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
function InSeq(s: seq<int>, x: int): bool
{
    exists i :: 0 <= i < |s| && s[i] == x
}

function ArrayContains(a: array<int>, x: int): bool
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

lemma ArrayContainsEquivInArray(a: array<int>, x: int)
    ensures ArrayContains(a, x) == InArray(a, x)
{
}

lemma InSeqImpliesInResult(s: seq<int>, x: int)
    ensures InSeq(s, x) <==> x in s
{
}

lemma AppendPreservesDistinct(s: seq<int>, x: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
    requires !InSeq(s, x)
    ensures forall i, j :: 0 <= i < j < |s + [x]| ==> (s + [x])[i] != (s + [x])[j]
{
    var s' := s + [x];
    assert |s'| == |s| + 1;
    assert s'[|s|] == x;
    
    forall i, j | 0 <= i < j < |s'|
        ensures s'[i] != s'[j]
    {
        if j < |s| {
            assert s'[i] == s[i] && s'[j] == s[j];
        } else {
            assert j == |s|;
            assert s'[j] == x;
            assert s'[i] == s[i];
            assert !InSeq(s, x);
            assert s[i] != x;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method DissimilarElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are either in a or b, but not in both or neither
    ensures forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
    result := [];
    
    // Add elements from array a that are not in array b
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in result ==> (InArray(a, x) && !InArray(b, x))
        invariant forall k, j :: 0 <= k < j < |result| ==> result[k] != result[j]
    {
        ArrayContainsEquivInArray(a, a[i]);
        ArrayContainsEquivInArray(b, a[i]);
        
        if !ArrayContains(b, a[i]) && !InSeq(result, a[i])
        {
            AppendPreservesDistinct(result, a[i]);
            result := result + [a[i]];
        }
        i := i + 1;
    }
    
    // Add elements from array b that are not in array a
    i := 0;
    while i < b.Length
        invariant 0 <= i <= b.Length
        invariant forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
        invariant forall k, j :: 0 <= k < j < |result| ==> result[k] != result[j]
    {
        ArrayContainsEquivInArray(a, b[i]);
        ArrayContainsEquivInArray(b, b[i]);
        
        if !ArrayContains(a, b[i]) && !InSeq(result, b[i])
        {
            AppendPreservesDistinct(result, b[i]);
            result := result + [b[i]];
        }
        i := i + 1;
    }
}
// </vc-code>