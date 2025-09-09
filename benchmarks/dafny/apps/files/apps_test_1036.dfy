/*
Given integers n and k, simulate a Rock-Paper-Scissors tournament among 2^k players.
Each player i has favorite hand from string s at position ((i mod n) + 1).
Tournament uses recursive bracket structure where Rock beats Scissors, 
Paper beats Rock, Scissors beats Paper, and ties go to the first player.
Return the favorite hand of the tournament winner.
*/

function winner(a: char, b: char): char
{
    if (a, b) == ('R', 'P') || (a, b) == ('P', 'S') || (a, b) == ('S', 'R') then b else a
}

predicate validRPSChar(c: char)
{
    c == 'R' || c == 'P' || c == 'S'
}

predicate validRPSString(s: string)
{
    forall i :: 0 <= i < |s| ==> validRPSChar(s[i])
}

predicate ValidInput(n: int, k: int, s: string)
{
    n > 0 && k >= 0 && |s| == n && validRPSString(s)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, s: string) returns (result: char)
    requires ValidInput(n, k, s)
    ensures validRPSChar(result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
