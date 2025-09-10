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

lemma TargetProductLemma(target: int, x: int, y: int, n: int)
  requires n > 0 && target == 6 * n && x >= target && y > 0
  ensures x * y >= target
{
  assert x >= target;
  assert y > 0;
  assert target > 0;
  assert x * y >= target * 1;
  assert target * 1 == target;
}

lemma DimensionConstraintLemma(x: int, y: int, a: int, b: int, target: int)
  requires a > 0 && b > 0 && target > 0
  requires (x == a && y == b) || (x == target && y == a) || (x == target && y == b)
  ensures (x >= a && y >= b) || (x >= b && y >= a)
{
  if x == a && y == b {
    assert x >= a && y >= b;
  } else if x == target && y == a {
    assert x >= b && y >= a;
  } else {
    assert x == target && y == b;
    assert x >= a && y >= b;
  }
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
  
  if a * b >= target {
    x := a;
    y := b;
    assert x >= a && y >= b;
    ProductLowerBound(x, y, a, b, n);
    assert x * y >= a * b >= target;
  } else {
    x := target;
    if a >= b {
      y := a;
      assert x == target && y == a;
      assert x >= b && y >= a;
    } else {
      y := b;
      assert x == target && y == b;
      assert x >= a && y >= b;
    }
    TargetProductLemma(target, x, y, n);
    assert x * y >= target;
  }
  
  var product := x * y;
  assert product >= target;
  
  result := [product, x, y];
  
  assert |result| == 3;
  assert result[0] == product && result[1] == x && result[2] == y;
  assert result[0] >= 6 * n;
  assert result[1] > 0 && result[2] > 0;
  assert result[0] == result[1] * result[2];
  assert (result[1] >= a && result[2] >= b) || (result[1] >= b && result[2] >= a);
}
// </vc-code>

