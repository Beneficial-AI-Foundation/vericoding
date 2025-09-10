predicate ValidInput(n: int, a: int, b: int)
{
  n > 0 && a > 0 && b > 0
}

predicate ValidOutput(result: seq<int>, n: int, a: int, b: int)
{
  |result| == 3 &&
  result[0] >= 6 * n &&
  result[1] > 0 && result[2] > 0 &&
  result[0] == result[1] * result[2] &&
  ((result[1] >= a && result[2] >= b) || (result[1] >= b && result[2] >= a))
}

// <vc-helpers>
// no helpers required
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int) returns (result: seq<int>)
  requires ValidInput(n, a, b)
  ensures ValidOutput(result, n, a, b)
// </vc-spec>
// <vc-code>
{
  var r1 := a;
  var r2 := b;
  while r1 * r2 < 6 * n
    invariant r1 == a
    invariant r2 >= b
    invariant r1 > 0
    invariant r2 > 0
    decreases 6 * n - r1 * r2
  {
    r2 := r2 + 1;
  }
  var r0 := r1 * r2;
  result := [r0, r1, r2];
}
// </vc-code>

