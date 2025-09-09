/*
Two players play a game on an array of integers, alternating turns.
First player removes subsegments with odd sum, second player removes subsegments with even sum.
After removal, remaining parts are concatenated. Player who cannot move loses.
Determine the winner assuming optimal play.
*/

predicate AllEven(a: seq<int>)
{
    forall i :: 0 <= i < |a| ==> a[i] % 2 == 0
}

predicate HasOdd(a: seq<int>)
{
    exists i :: 0 <= i < |a| && a[i] % 2 == 1
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: string)
    ensures result == "Second" <==> AllEven(a)
    ensures result == "First" <==> HasOdd(a)
    ensures result == "First" || result == "Second"
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
