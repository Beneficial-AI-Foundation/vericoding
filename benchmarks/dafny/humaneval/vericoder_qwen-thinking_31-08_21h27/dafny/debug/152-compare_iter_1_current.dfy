

// <vc-helpers>

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
  var r := new int[scores.Length];
  var i := 0;
  while i < r.Length {
    invariant i <= r.Length;
    invariant forall j :: 0 <= j < i ==> r[j] == abs(scores[j] - guesses[j]);
    r[i] := abs(scores[i] - guesses[i]);
    i := i + 1;
  }
  return r;
}
// </vc-code>

function abs(x: int): int
    ensures 0 <= abs(x)
{
  if x < 0 then -x else x
}
// pure-end