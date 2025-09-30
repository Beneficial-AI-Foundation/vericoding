// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ArrayConcat(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    ensures
        |result| == |a| + |b| &&
        (forall i :: 0 <= i < |a| ==> result[i] == a[i]) &&
        (forall i :: 0 <= i < |b| ==> result[i + |a|] == b[i])
// </vc-spec>
// <vc-code>
{
  result := a + b;
}
// </vc-code>
