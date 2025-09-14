// <vc-preamble>
type NestedSeq = seq<seq<int>>
// </vc-preamble>

// <vc-helpers>
lemma AllLengthsEqual(s: NestedSeq)
    requires |s| > 0
    requires forall k :: 0 <= k < |s| ==> |s[k]| == |s[0]|
    ensures forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> |s[i]| == |s[j]|
{}
// </vc-helpers>

// <vc-spec>
method AllSequenceEqualLength(s: NestedSeq) returns (r: bool)
    requires |s| > 0
    ensures r == (forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> |s[i]| == |s[j]|)
// </vc-spec>
// <vc-code>
{
    var i := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant forall k :: 0 <= k < i ==> |s[k]| == |s[0]|
    {
        if |s[i]| != |s[0]| {
            r := false;
            return;
        }
        i := i + 1;
    }
    r := true;
    AllLengthsEqual(s);
}
// </vc-code>
