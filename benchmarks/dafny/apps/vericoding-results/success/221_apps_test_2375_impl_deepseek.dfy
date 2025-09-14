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
lemma AliceWinsImpliesNotBrownWins(X: int, Y: int)
  requires ValidInput(X, Y)
  ensures AliceWins(X, Y) ==> !BrownWins(X, Y)
{
}

lemma BrownWinsImpliesNotAliceWins(X: int, Y: int)
  requires ValidInput(X, Y)
  ensures BrownWins(X, Y) ==> !AliceWins(X, Y)
{
}

lemma ExactlyOneWins(X: int, Y: int)
  requires ValidInput(X, Y)
  ensures AliceWins(X, Y) || BrownWins(X, Y)
  ensures AliceWins(X, Y) ==> !BrownWins(X, Y)
  ensures BrownWins(X, Y) ==> !AliceWins(X, Y)
{
  if Abs(X - Y) > 1 {
    assert AliceWins(X, Y);
    assert !BrownWins(X, Y);
  } else {
    assert BrownWins(X, Y);
    assert !AliceWins(X, Y);
  }
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
  } else {
    winner := "Brown";
  }
}
// </vc-code>

