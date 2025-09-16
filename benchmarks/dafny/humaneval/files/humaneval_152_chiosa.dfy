// <vc-preamble>
// ======= SPEC REQUIREMENTS =======
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
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
function abs(x: int): int
{
  if x >= 0 then x else -x
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
function compare(game: seq<int>, guess: seq<int>): seq<int>
  requires ValidInput(game, guess)
  ensures ValidOutput(game, guess, compare(game, guess))
// </vc-spec>
// <vc-code>
{
  seq(|game|, i requires 0 <= i < |game| => 
    var diff := game[i] - guess[i];
    if diff >= 0 then diff else -diff
  )
}
// </vc-code>
