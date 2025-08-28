method Compare(scores: array<int>, guesses: array<int>) returns (result: array<int>)
  // pre-conditions-start
  requires scores.Length == guesses.Length
  // pre-conditions-end
  // post-conditions-start
  ensures result.Length == scores.Length
  ensures forall i :: 0 <= i < result.Length ==> result[i] == abs(scores[i] - guesses[i])
  // post-conditions-end
{
  // impl-start
  result := new int[scores.Length];
  var i := 0;
  while i < scores.Length
    // invariants-start
    invariant 0 <= i <= scores.Length
    invariant result.Length == scores.Length
    invariant forall k :: 0 <= k < i ==> result[k] == abs(scores[k] - guesses[k])
    // invariants-end
  {
    result[i] := abs(scores[i] - guesses[i]);
    i := i + 1;
  }
  // impl-end
}

function abs(x: int): int
    ensures 0 <= abs(x)
{
  if x < 0 then -x else x
}
// pure-end
