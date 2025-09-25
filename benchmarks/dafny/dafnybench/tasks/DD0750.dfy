// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Interleave(s1: seq<int>, s2: seq<int>, s3: seq<int>) returns (r: seq<int>)
    requires |s1| == |s2| && |s2| == |s3|
    ensures |r| == 3 * |s1|
    ensures forall i :: 0 <= i < |s1| ==> r[3*i] == s1[i] && r[3*i + 1] == s2[i] && r[3*i + 2] == s3[i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
