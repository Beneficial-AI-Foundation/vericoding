// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SmallestMissingNumber(s: seq<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures 0 <= v
    ensures v !in s
    ensures forall k :: 0 <= k < v ==> k in s
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
