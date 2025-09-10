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
lemma ProductLowerBound(x: int, y: int, a: int, b: int, n: int)
  requires x >= a && y >= b && a > 0 && b > 0 && n > 0
  ensures x * y >= a * b
{
}

lemma MinProductBound(a: int, b: int, n: int)
  requires a > 0 && b > 0 && n > 0
  ensures a * b >= 1
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int) returns (result: seq<int>)
  requires ValidInput(n, a, b)
  ensures ValidOutput(result, n, a, b)
// </vc-spec>
// <vc-code>
{
  var target := 6 * n;
  var x, y;
  
  if a >= b {
    x := if a >= target then a else target;
    y := if a >= target then b else 1;
  } else {
    x := if b >= target then b else target;
    y := if b >= target then a else 1;
  }
  
  var product := x * y;
  if product < target {
    product := target;
  }
  
  result := [product, x, y];
}
// </vc-code>

