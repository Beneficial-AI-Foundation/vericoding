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
lemma ProductProperty(n: int, a: int, b: int)
  requires n > 0 && a > 0 && b > 0
  ensures max(2*n, a) * max(3*n, b) >= 6 * n
{
  var x := max(2*n, a);
  var y := max(3*n, b);
  
  assert x >= 2*n;
  assert y >= 3*n;
  assert x * y >= 2*n * 3*n;
  assert 2*n * 3*n == 6*n*n;
  assert n >= 1;
  assert 6*n*n >= 6*n;
}

function max(x: int, y: int): int
{
  if x >= y then x else y
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int) returns (result: seq<int>)
  requires ValidInput(n, a, b)
  ensures ValidOutput(result, n, a, b)
// </vc-spec>
// <vc-code>
{
  var x := max(2*n, a);
  var y := max(3*n, b);
  
  ProductProperty(n, a, b);
  
  result := [x * y, x, y];
  
  assert result[0] == result[1] * result[2];
  assert result[1] >= a;
  assert result[2] >= b;
  assert result[1] >= 2*n && result[2] >= 3*n;
  assert result[0] == x * y >= 6 * n;
}
// </vc-code>

