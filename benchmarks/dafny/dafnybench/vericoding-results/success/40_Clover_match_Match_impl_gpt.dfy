

// <vc-helpers>
// No helpers needed
// </vc-helpers>

// <vc-spec>
method Match(s: string, p: string) returns (b: bool)
  requires |s| == |p|
  ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
// </vc-spec>
// <vc-code>
{
  b := (forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?');
}
// </vc-code>

