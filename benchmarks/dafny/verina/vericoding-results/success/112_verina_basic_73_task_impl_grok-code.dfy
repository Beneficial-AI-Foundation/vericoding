// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MatchStrings(s: string, p: string) returns (result: bool)
    requires |s| == |p|
    ensures result == (forall n :: 0 <= n < |s| ==> 
        (s[n] == p[n] || p[n] == '?'))
// </vc-spec>
// <vc-code>
{
  result := true;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> (s[k] == p[k] || p[k] == '?')
  {
    if !(s[i] == p[i] || p[i] == '?') {
      result := false;
      break;
    }
    i := i + 1;
  }
}
// </vc-code>
