// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Concat(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    ensures |result| == |a| + |b|
    ensures forall k :: 0 <= k < |a| ==> result[k] == a[k]
    ensures forall k :: 0 <= k < |b| ==> result[k + |a|] == b[k]
// </vc-spec>
// <vc-code>
{
  result := a + b;
}
// </vc-code>
