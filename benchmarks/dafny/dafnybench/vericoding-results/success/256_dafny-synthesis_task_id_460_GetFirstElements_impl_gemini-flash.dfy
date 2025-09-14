

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method GetFirstElements(lst: seq<seq<int>>) returns (result: seq<int>)
    requires forall i :: 0 <= i < |lst| ==> |lst[i]| > 0
    ensures |result| == |lst|
    ensures forall i :: 0 <= i < |result| ==> result[i] == lst[i][0]
// </vc-spec>
// <vc-code>
{
    var result_seq: seq<int> := [];
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant |result_seq| == i
        invariant forall k :: 0 <= k < i ==> result_seq[k] == lst[k][0]
    {
        result_seq := result_seq + [lst[i][0]];
        i := i + 1;
    }
    return result_seq;
}
// </vc-code>

