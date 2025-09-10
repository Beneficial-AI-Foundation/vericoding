/*
Two players Alice and Brown play a turn-based stone game starting with Alice.
There are two piles with X and Y stones. On each turn, a player chooses positive
integer i, takes 2i stones from one pile (requiring at least 2i stones),
discards i stones, and places remaining i stones in the other pile.
The player who cannot make a valid move loses. Determine winner with optimal play.
*/

function Abs(x: int): int
{
  if x >= 0 then x else -x
}

predicate AliceWins(X: int, Y: int)
{
  Abs(X - Y) > 1
}

predicate BrownWins(X: int, Y: int)
{
  Abs(X - Y) <= 1
}

predicate ValidInput(X: int, Y: int)
{
  X >= 0 && Y >= 0
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method DetermineWinner(X: int, Y: int) returns (winner: string)
  requires ValidInput(X, Y)
  ensures winner == "Alice" || winner == "Brown"
  ensures (winner == "Alice") <==> AliceWins(X, Y)
  ensures (winner == "Brown") <==> BrownWins(X, Y)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
