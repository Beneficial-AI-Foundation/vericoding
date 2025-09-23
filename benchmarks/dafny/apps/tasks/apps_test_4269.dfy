// <vc-preamble>
predicate IsHardToEnter(s: string)
    requires |s| == 4
{
    s[0] == s[1] || s[1] == s[2] || s[2] == s[3]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| == 4
    ensures result == "Bad" <==> IsHardToEnter(s)
    ensures result == "Good" <==> !IsHardToEnter(s)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
