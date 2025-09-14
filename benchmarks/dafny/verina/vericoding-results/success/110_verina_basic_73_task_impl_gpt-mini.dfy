// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function charMatches(c: char, pch: char): bool { c == pch || pch == '?' }
predicate AllMatch(s: string, p: string) { |s| == |p| && forall n :: 0 <= n < |s| ==> charMatches(s[n], p[n]) }
// </vc-helpers>

// <vc-spec>
method MatchStrings(s: string, p: string) returns (result: bool)
    requires |s| == |p|
    ensures result == (forall n :: 0 <= n < |s| ==> 
        (s[n] == p[n] || p[n] == '?'))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var r := true;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant r == (forall k :: 0 <= k < i ==> charMatches(s[k], p[k]))
    decreases |s| - i
  {
    r := r && charMatches(s[i], p[i]);
    i := i + 1;
  }
  result := r;
}
// </vc-code>
