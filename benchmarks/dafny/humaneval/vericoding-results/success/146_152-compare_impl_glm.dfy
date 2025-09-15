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
/* code modified by LLM (iteration 2): Added loop invariants to help verifier */
{
  result := new int[scores.Length];
  for i := 0 to scores.Length
    invariant 0 <= i <= scores.Length
    invariant forall j :: 0 <= j < i ==> result[j] == abs(scores[j] - guesses[j])
  {
    result[i] := abs(scores[i] - guesses[i]);
  }
}
// </vc-code>
