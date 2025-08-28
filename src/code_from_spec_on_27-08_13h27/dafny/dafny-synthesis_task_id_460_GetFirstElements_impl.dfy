// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method GetFirstElements(lst: seq<seq<int>>) returns (result: seq<int>)
    requires forall i :: 0 <= i < |lst| ==> |lst[i]| > 0
    ensures |result| == |lst|
    ensures forall i :: 0 <= i < |result| ==> result[i] == lst[i][0]
// </vc-spec>
// </vc-spec>

// <vc-code>
method GetFirstElementsImpl(lst: seq<seq<int>>) returns (result: seq<int>)
    requires forall i :: 0 <= i < |lst| ==> |lst[i]| > 0
    ensures |result| == |lst|
    ensures forall i :: 0 <= i < |result| ==> result[i] == lst[i][0]
{
    result := [];
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> result[k] == lst[k][0]
    {
        result := result + [lst[i][0]];
        i := i + 1;
    }
}
// </vc-code>
