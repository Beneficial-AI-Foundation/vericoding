// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function AllMatch(s: string, p: string): bool
  requires |s| == |p|
{
  forall n :: 0 <= n < |s| ==> (s[n] == p[n] || p[n] == '?')
}
// </vc-helpers>

// <vc-spec>
method MatchStrings(s: string, p: string) returns (result: bool)
    requires |s| == |p|
    ensures result == (forall n :: 0 <= n < |s| ==> 
        (s[n] == p[n] || p[n] == '?'))
// </vc-spec>
// <vc-code>
{
  result := AllMatch(s, p);
}
// </vc-code>
