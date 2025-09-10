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
predicate {:opaque} AliceWins(X: int, Y: int)
{
  Abs(X - Y) > 1
}

predicate {:opaque} BrownWins(X: int, Y: int)
{
  Abs(X - Y) <= 1
}
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
    assert AliceWins(X, Y); // Reveal AliceWins
    assert !BrownWins(X, Y); // Reveal BrownWins to prove it's false
  } else {
    winner := "Brown";
    assert BrownWins(X, Y); // Reveal BrownWins
    assert !AliceWins(X, Y); // Reveal AliceWins to prove it's false
  }
}
// </vc-code>

