// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function MaxSeq(s: seq<int>): int
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> MaxSeq(s) >= s[i]
  ensures exists j :: 0 <= j < |s| && MaxSeq(s) == s[j]
{
  if |s| == 1 then s[0] else if s[0] >= MaxSeq(s[1..]) then s[0] else MaxSeq(s[1..])
}
// </vc-helpers>

// <vc-spec>
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a.Length > 0
    ensures result == (forall i :: 0 <= i < a.Length ==> n > a[i])
// </vc-spec>
// <vc-code>
{
  result := n > MaxSeq(a[..]);
}
// </vc-code>
