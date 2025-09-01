

// <vc-helpers>
// No changes needed, the `abs` function is already defined correctly in the POSTAMBLE.
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
{
  var n := scores.Length;
  var finalResult := new int[n]; // Renamed local variable to avoid conflict with the method's return parameter.

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant finalResult.Length == n
    invariant forall k :: 0 <= k < i ==> finalResult[k] == abs(scores[k] - guesses[k])
  {
    finalResult[i] := abs(scores[i] - guesses[i]);
    i := i + 1;
  }
  return finalResult;
}
// </vc-code>

function abs(x: int): int
    ensures 0 <= abs(x)
{
  if x < 0 then -x else x
}
// pure-end