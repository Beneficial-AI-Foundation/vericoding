// <vc-preamble>
type NestedSeq = seq<seq<int>>
// </vc-preamble>

// <vc-helpers>
function AllHaveLength(s: NestedSeq, len: int): bool {
  forall i :: 0 <= i < |s| ==> |s[i]| == len
}
// </vc-helpers>

// <vc-spec>
method AllSequenceEqualLength(s: NestedSeq) returns (r: bool)
    requires |s| > 0
    ensures r == (forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> |s[i]| == |s[j]|)
// </vc-spec>
// <vc-code>
{
  var firstLen := |s[0]|;
  r := AllHaveLength(s, firstLen);
}
// </vc-code>
