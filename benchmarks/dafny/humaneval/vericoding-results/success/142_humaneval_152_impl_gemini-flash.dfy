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
  /* code modified by LLM (iteration 4): Fixed compilation error by changing the loop upper bound to `|game|` instead of `|game| - 1` when using new int[|game|], and fixed postcondition error by adding `&& forall j :: 0 <= j < i ==> res_arr[j] >= 0` to loop invariant.
*/
  var res_arr: array<int> := new int[|game|];
  for i := 0 to |game|
    invariant 0 <= i <= |game|
    invariant res_arr.Length == |game|
    invariant forall j :: 0 <= j < i ==> res_arr[j] == abs(game[j] - guess[j])
    invariant forall j :: 0 <= j < i ==> res_arr[j] >= 0
  {
    if i < |game| {
      res_arr[i] := abs(game[i] - guess[i]);
    }
  }
  return res_arr[..];
}
// </vc-code>
