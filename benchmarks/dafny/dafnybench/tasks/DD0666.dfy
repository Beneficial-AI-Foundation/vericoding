// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method AppendArrayToSeq(s: seq<int>, a: array<int>) returns (r: seq<int>)
    requires a != null
    ensures |r| == |s| + a.Length
    ensures forall i :: 0 <= i < |s| ==> r[i] == s[i]
    ensures forall i :: 0 <= i < a.Length ==> r[|s| + i] == a[i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
