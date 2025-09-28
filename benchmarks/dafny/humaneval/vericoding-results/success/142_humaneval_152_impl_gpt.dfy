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
/* helper modified by LLM (iteration 2): recursive computation of absolute differences between two equal-length sequences */
function DiffSeq(game: seq<int>, guess: seq<int>): seq<int>
  requires |game| == |guess|
  ensures |DiffSeq(game, guess)| == |game|
  ensures forall i :: 0 <= i < |game| ==> DiffSeq(game, guess)[i] == abs(game[i] - guess[i])
  ensures forall i :: 0 <= i < |DiffSeq(game, guess)| ==> DiffSeq(game, guess)[i] >= 0
  decreases |game|
{
  if |game| == 0 then
    []
  else
    [abs(game[0] - guess[0])] + DiffSeq(game[1..], guess[1..])
}

// </vc-helpers>

// <vc-spec>
method compare(game: seq<int>, guess: seq<int>) returns (result: seq<int>)
  requires ValidInput(game, guess)
  ensures ValidOutput(game, guess, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute result via helper function ensuring ValidOutput */
  result := DiffSeq(game, guess);
}
// </vc-code>
