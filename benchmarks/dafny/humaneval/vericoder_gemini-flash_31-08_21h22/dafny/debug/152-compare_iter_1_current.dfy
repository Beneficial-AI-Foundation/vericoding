

// <vc-helpers>
function abs(x: int): int
  ensures 0 <= abs(x)
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
{
  var n := scores.Length;
  var result_arr := new int[n];

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result_arr.Length == n
    invariant forall k :: 0 <= k < i ==> result_arr[k] == abs(scores[k] - guesses[k])
  {
    result_arr[i] := abs(scores[i] - guesses[i]);
    i := i + 1;
  }
  return result_arr;
}
// </vc-code>

function abs(x: int): int
    ensures 0 <= abs(x)
{
  if x < 0 then -x else x
}
// pure-end