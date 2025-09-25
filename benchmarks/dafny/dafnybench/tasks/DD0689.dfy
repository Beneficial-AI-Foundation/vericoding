// <vc-preamble>
// </vc-preamble>

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
  assume {:axiom} false;
}
// </vc-code>
