

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Match(s: string, p: string) returns (b: bool)
  requires |s| == |p|
  ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall n :: 0 <= n < i ==> s[n] == p[n] || p[n] == '?'
  {
    if s[i] != p[i] && p[i] != '?' {
      b := false;
      return;
    }
    i := i + 1;
  }
  b := true;
}
// </vc-code>

