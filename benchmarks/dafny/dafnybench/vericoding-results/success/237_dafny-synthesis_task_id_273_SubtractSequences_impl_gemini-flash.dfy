

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SubtractSequences(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] - b[i]
// </vc-spec>
// <vc-code>
{
    var result_seq: seq<int> := [];
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant |result_seq| == i
        invariant forall k :: 0 <= k < i ==> result_seq[k] == a[k] - b[k]
    {
        result_seq := result_seq + [a[i] - b[i]];
        i := i + 1;
    }
    return result_seq;
}
// </vc-code>

