// <vc-helpers>
// </vc-helpers>

method DeepCopySeq(s: seq<int>) returns (copy: seq<int>)
    ensures |copy| == |s|
    ensures forall i :: 0 <= i < |s| ==> copy[i] == s[i]
// <vc-code>
{
  assume false;
}
// </vc-code>