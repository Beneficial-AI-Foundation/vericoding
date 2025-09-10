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

lemma ProductMonotonic(x1: int, y1: int, x2: int, y2: int)
  requires x1 > 0 && y1 > 0 && x2 >= x1 && y2 >= y1
  ensures x2 * y2 >= x1 * y1
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
  
  // Simple approach: ensure x * y >= target and satisfy dimension constraints
  if a * b >= target {
    x := a;
    y := b;
  } else {
    // Scale up to meet target
    x := target;
    y := if a >= b then b else a;
  }
  
  var product := x * y;
  
  result := [product, x, y];
}
// </vc-code>

