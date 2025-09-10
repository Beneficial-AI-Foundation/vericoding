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
  
  // Choose dimensions ensuring we meet the size constraints
  if target >= a && target >= b {
    // target is large enough for both dimensions
    x := target;
    y := 1;
    // Ensure we satisfy the constraint by making x the larger of a,b
    if a >= b {
      // x >= target >= a >= b, y = 1 >= b only if b = 1
      if b > 1 {
        y := b;
      }
    } else {
      // x >= target >= b >= a, y = 1 >= a only if a = 1  
      if a > 1 {
        y := a;
      }
    }
  } else {
    // target is not large enough, use a and b directly
    x := if a >= b then a else b;
    y := if a >= b then b else a;
  }
  
  var product := x * y;
  if product < target {
    // Need to increase product to meet target
    if x < target {
      x := target;
      product := x * y;
    }
  }
  
  result := [product, x, y];
}
// </vc-code>

