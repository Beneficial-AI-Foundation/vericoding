// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function matchChar(c: char, pc: char): bool
{
  c == pc || pc == '?'
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
  result := (forall n :: 0 <= n < |s| ==> matchChar(s[n], p[n]));
}
// </vc-code>
