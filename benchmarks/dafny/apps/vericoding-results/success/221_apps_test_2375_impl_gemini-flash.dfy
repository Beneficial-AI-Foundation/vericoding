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
// No changes needed in helpers, remove duplicate predicate definitions by moving them to the preamble
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
  if Abs(X - Y) > 1 {
    winner := "Alice";
    assert AliceWins(X, Y);
    assert !BrownWins(X, Y);
  } else {
    winner := "Brown";
    assert BrownWins(X, Y);
    assert !AliceWins(X, Y);
  }
}
// </vc-code>

