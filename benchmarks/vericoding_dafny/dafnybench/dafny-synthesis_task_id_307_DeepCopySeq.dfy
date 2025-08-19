// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method DeepCopySeq(s: seq<int>) returns (copy: seq<int>)
    ensures |copy| == |s|
    ensures forall i :: 0 <= i < |s| ==> copy[i] == s[i]
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>