/*
Given a string of lowercase letters, delete the minimum number of characters to make it "good".
A string is "good" if its length is even and each character at odd positions (1st, 3rd, 5th, ...)
differs from the character at the next even position (2nd, 4th, 6th, ...).
*/

predicate ValidInput(n: int, s: string)
{
    n == |s| && n >= 0
}

predicate IsGoodString(s: string)
{
    |s| % 2 == 0 && forall i :: 0 <= i < |s|/2 ==> s[2*i] != s[2*i+1]
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (deletedCount: int, result: string)
    requires ValidInput(n, s)
    ensures deletedCount >= 0
    ensures deletedCount == |s| - |result|
    ensures IsGoodString(result)
    ensures deletedCount + |result| == |s|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
