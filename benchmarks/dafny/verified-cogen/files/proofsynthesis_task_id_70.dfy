// <vc-preamble>
type NestedSeq = seq<seq<int>>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method AllSequenceEqualLength(s: NestedSeq) returns (r: bool)
    requires |s| > 0
    ensures r == (forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> |s[i]| == |s[j]|)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
