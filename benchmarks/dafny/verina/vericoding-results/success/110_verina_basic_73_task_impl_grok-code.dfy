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
  var matches := true;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> (s[j] == p[j] || p[j] == '?')
    invariant matches <==> forall j :: 0 <= j < i ==> (s[j] == p[j] || p[j] == '?')
  {
    if !(s[i] == p[i] || p[i] == '?') {
      matches := false;
      break;
    }
    i := i + 1;
  }
  result := matches;
}
// </vc-code>
