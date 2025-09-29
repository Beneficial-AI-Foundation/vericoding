// <vc-preamble>
predicate ValidInput(game: seq<int>, guess: seq<int>)
{
  |game| == |guess|
}

predicate ValidOutput(game: seq<int>, guess: seq<int>, result: seq<int>)
  requires |game| == |guess|
{
  && |result| == |game|
  && (forall i :: 0 <= i < |game| ==> result[i] == abs(game[i] - guess[i]))
  && (forall i :: 0 <= i < |result| ==> result[i] >= 0)
}
function abs(x: int): int
{
  if x >= 0 then x else -x
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method compare(game: seq<int>, guess: seq<int>) returns (result: seq<int>)
  requires ValidInput(game, guess)
  ensures ValidOutput(game, guess, result)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |game|
    invariant 0 <= i <= |game|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == abs(game[j] - guess[j])
    invariant forall j :: 0 <= j < i ==> result[j] >= 0
  {
    result := result + [abs(game[i] - guess[i])];
    i := i + 1;
  }
}
// </vc-code>
