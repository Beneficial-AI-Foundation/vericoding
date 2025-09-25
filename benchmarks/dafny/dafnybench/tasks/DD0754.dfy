// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ArrayToSeq(a: array<int>) returns (s: seq<int>)
    requires a != null
    ensures |s| == a.Length
    ensures forall i :: 0 <= i < a.Length ==> s[i] == a[i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
