// <vc-preamble>
function abs(x: int): int
    ensures 0 <= abs(x)
{
  if x < 0 then -x else x
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Compare(scores: array<int>, guesses: array<int>) returns (result: array<int>)

  requires scores.Length == guesses.Length

  ensures result.Length == scores.Length
  ensures forall i :: 0 <= i < result.Length ==> result[i] == abs(scores[i] - guesses[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := new int[scores.Length];
  while i < scores.Length
    invariant 0 <= i <= scores.Length
    invariant forall k :: 0 <= k < i ==> result[k] == abs(scores[k] - guesses[k])
  {
    result[i] := abs(scores[i] - guesses[i]);
    i := i + 1;
  }
  return result;
}
// </vc-code>
