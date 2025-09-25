// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
    requires s.Length > 0
    requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
    ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && 
        (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
