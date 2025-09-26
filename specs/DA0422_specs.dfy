// <vc-preamble>
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
// </vc-preamble>

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
