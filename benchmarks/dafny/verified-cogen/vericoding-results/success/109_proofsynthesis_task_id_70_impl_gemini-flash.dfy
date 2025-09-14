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
/* code modified by LLM (iteration 5): fixed loop invariant and postcondition to handle the base case. The loop should iterate up to but not include `|s|`, and the invariant for `allEqual` should reflect this */
{
    var len0 := |s[0]|;
    var allEqual := true;
    for i := 1 to |s|
        invariant 1 <= i <= |s| + 1
        invariant allEqual == (forall k :: 0 <= k < i && k < |s| ==> |s[k]| == len0)
    {
        if i < |s| && |s[i]| != len0 {
            allEqual := false;
        }
    }
    return allEqual;
}
// </vc-code>
