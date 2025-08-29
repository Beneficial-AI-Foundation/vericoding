// <vc-helpers>
function absolute(x: int): int
  ensures 0 <= absolute(x)
{
  if x < 0 then -x else x
}
// </vc-helpers>

// <vc-spec>
method Compare(scores: array<int>, guesses: array<int>) returns (result: array<int>)
  // pre-conditions-start
  requires scores.Length == guesses.Length
  // pre-conditions-end
  // post-conditions-start
  ensures result.Length == scores.Length
  ensures forall i :: 0 <= i < result.Length ==> result[i] == abs(scores[i] - guesses[i])
  // post-conditions-end
// </vc-spec>
// <vc-code>
method CompareArrays(scores: array<int>, guesses: array<int>) returns (result: array<int>)
  requires scores.Length == guesses.Length
  ensures result.Length == scores.Length
  ensures forall i :: 0 <= i < result.Length ==> result[i] == absolute(scores[i] - guesses[i])
{
  result := new int[scores.Length];
  for i := 0 to scores.Length
    invariant 0 <= i <= scores.Length
    invariant forall j :: 0 <= j < i ==> result[j] == absolute(scores[j] - guesses[j])
  {
    result[i] := absolute(scores[i] - guesses[i]);
  }
}
// </vc-code>

function abs(x: int): int
    ensures 0 <= abs(x)
{
  if x < 0 then -x else x
}
// pure-end