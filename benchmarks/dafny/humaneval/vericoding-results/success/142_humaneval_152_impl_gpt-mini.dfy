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
lemma AbsNonNeg(x: int)
  ensures abs(x) >= 0
{
  if x >= 0 {
    assert abs(x) == x;
    assert x >= 0;
  } else {
    assert abs(x) == -x;
    assert -x >= 0;
  }
}
// </vc-helpers>

// <vc-spec>
method compare(game: seq<int>, guess: seq<int>) returns (result: seq<int>)
  requires ValidInput(game, guess)
  ensures ValidOutput(game, guess, result)
// </vc-spec>
// <vc-code>
{
  var len := |game|;
  var A := new int[len];
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant forall j :: 0 <= j < i ==> A[j] == abs(game[j] - guess[j])
    invariant forall j :: 0 <= j < i ==> A[j] >= 0
  {
    A[i] := abs(game[i] - guess[i]);
    i := i + 1;
  }
  result := A[..];
}
// </vc-code>
