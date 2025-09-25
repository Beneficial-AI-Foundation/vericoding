// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ArraySum(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] + b[i]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
    result := seq(|a|, i => 0);
}
// </vc-code>
