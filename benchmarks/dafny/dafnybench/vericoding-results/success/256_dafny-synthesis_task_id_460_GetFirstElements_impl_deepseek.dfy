

// <vc-helpers>
lemma Lemma_LengthOfSequenceAfterAppend<T>(s: seq<T>, e: T)
    ensures |s + [e]| == |s| + 1
{
}

lemma Lemma_ElementAtAppendedPosition<T>(s: seq<T>, e: T, j: int)
    requires 0 <= j < |s| + 1
    ensures j < |s| ==> (s + [e])[j] == s[j]
    ensures j == |s| ==> (s + [e])[j] == e
{
}
// </vc-helpers>

// <vc-spec>
method GetFirstElements(lst: seq<seq<int>>) returns (result: seq<int>)
    requires forall i :: 0 <= i < |lst| ==> |lst[i]| > 0
    ensures |result| == |lst|
    ensures forall i :: 0 <= i < |result| ==> result[i] == lst[i][0]
// </vc-spec>
// <vc-code>
{
    result := [];
    var index := 0;
    while index < |lst|
        invariant 0 <= index <= |lst|
        invariant |result| == index
        invariant forall j :: 0 <= j < index ==> result[j] == lst[j][0]
    {
        var elem := lst[index][0];
        result := result + [elem];
        index := index + 1;
    }
}
// </vc-code>

