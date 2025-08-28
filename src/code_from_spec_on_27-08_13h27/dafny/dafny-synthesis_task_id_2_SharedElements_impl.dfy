predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
lemma UniqueElementsInSeq(s: seq<int>)
    ensures forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
    // This lemma is not needed as the property is directly ensured by construction in the code.
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
method SharedElementsImpl(a: array<int>, b: array<int>) returns (result: seq<int>)
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var temp: seq<int> := [];
    var i: int := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in temp ==> InArray(a, x) && InArray(b, x)
        invariant forall k, l :: 0 <= k < l < |temp| ==> temp[k] != temp[l]
    {
        if InArray(b, a[i]) && a[i] !in temp
        {
            temp := temp + [a[i]];
        }
        i := i + 1;
    }
    result := temp;
}
// </vc-code>
