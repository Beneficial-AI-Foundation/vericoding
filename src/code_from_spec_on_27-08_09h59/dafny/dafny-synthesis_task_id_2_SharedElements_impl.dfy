predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
lemma InArrayExists(a: array<int>, x: int, idx: int)
    requires 0 <= idx < a.Length
    requires a[idx] == x
    ensures InArray(a, x)
{
}

predicate SeqContains(s: seq<int>, x: int)
{
    exists i :: 0 <= i < |s| && s[i] == x
}

lemma SeqContainsImpliesIn(s: seq<int>, x: int)
    ensures SeqContains(s, x) <==> x in s
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SharedElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in both a and b
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    result := [];
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
        invariant forall k, j :: 0 <= k < j < |result| ==> result[k] != result[j]
    {
        var current := a[i];
        
        if InArray(b, current) && current !in result {
            result := result + [current];
            InArrayExists(a, current, i);
        }
        
        i := i + 1;
    }
}
// </vc-code>
