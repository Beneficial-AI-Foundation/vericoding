

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ElementWiseDivision(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
// </vc-spec>
// <vc-code>
{
    var result_seq: seq<int> := [];
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant |result_seq| == i
        invariant forall j :: 0 <= j < i ==> result_seq[j] == a[j] / b[j]
    {
        result_seq := result_seq + [a[i] / b[i]];
        i := i + 1;
    }
    return result_seq;
}
// </vc-code>

