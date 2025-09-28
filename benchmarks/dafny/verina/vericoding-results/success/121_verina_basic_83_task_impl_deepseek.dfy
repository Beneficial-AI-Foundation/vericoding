// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ConcatSeq(a: seq<int>, b: seq<int>): seq<int>
    ensures |ConcatSeq(a, b)| == |a| + |b|
    ensures forall k :: 0 <= k < |a| ==> ConcatSeq(a, b)[k] == a[k]
    ensures forall k :: 0 <= k < |b| ==> ConcatSeq(a, b)[k + |a|] == b[k]
{
    if |a| == 0 then
        b
    else
        [a[0]] + ConcatSeq(a[1..], b)
}
// </vc-helpers>

// <vc-spec>
method Concat(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    ensures |result| == |a| + |b|
    ensures forall k :: 0 <= k < |a| ==> result[k] == a[k]
    ensures forall k :: 0 <= k < |b| ==> result[k + |a|] == b[k]
// </vc-spec>
// <vc-code>
{
    result := ConcatSeq(a, b);
}
// </vc-code>
