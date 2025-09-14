

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Match(s: string, p: string) returns (b: bool)
  requires |s| == |p|
  ensures b <==> forall n :: 0 <= n < |s| ==> s[n] == p[n] || p[n] == '?'
// </vc-spec>
// <vc-code>
{
  b := true;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant b <==> forall k :: 0 <= k < i ==> (s[k] == p[k] || p[k] == '?')
  {
    b := b && (s[i] == p[i] || p[i] == '?');
    i := i + 1;
  }
}
// </vc-code>

