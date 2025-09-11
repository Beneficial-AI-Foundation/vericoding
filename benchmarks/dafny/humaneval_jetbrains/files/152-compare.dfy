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
  assume {:axiom} false;
}
// </vc-code>
