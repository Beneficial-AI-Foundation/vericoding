predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
lemma InArrayIndex(a: array<int>, x: int, i: int)
    requires 0 <= i < a.Length
    requires a[i] == x
    ensures InArray(a, x)
{
    // Witness that x is in array a at index i
}

predicate InSeq(s: seq<int>, x: int)
{
    exists i :: 0 <= i < |s| && s[i] == x
}

lemma NotInSeqImpliesAllDifferent(s: seq<int>, x: int)
    requires !InSeq(s, x)
    ensures forall i :: 0 <= i < |s| ==> s[i] != x
{
}
// </vc-helpers>

// <vc-spec>
method SharedElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in both a and b
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
    result := [];
    
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in result ==> InArray(a, x) && InArray(b, x)
        invariant forall j, k :: 0 <= j < k < |result| ==> result[j] != result[k]
    {
        if InArray(b, a[i]) && !InSeq(result, a[i]) {
            InArrayIndex(a, a[i], i);
            result := result + [a[i]];
        }
    }
}
// </vc-code>

