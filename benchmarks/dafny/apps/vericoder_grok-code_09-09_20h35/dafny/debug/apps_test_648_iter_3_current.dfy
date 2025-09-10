predicate ValidInput(m: int, b: int)
{
  1 <= m <= 1000 && 1 <= b <= 10000
}

function f(x: int, y: int): int
  requires x >= 0 && y >= 0
{
  (x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2
}

predicate ValidRectangleCorner(k: int, m: int, b: int)
{
  0 <= k && b - k >= 0
}

function RectangleValue(k: int, m: int, b: int): int
  requires ValidRectangleCorner(k, m, b)
  requires m >= 1
{
  f(k * m, b - k)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(m: int, b: int) returns (result: int)
  requires ValidInput(m, b)
  ensures result >= -1
  ensures forall k :: ValidRectangleCorner(k, m, b) ==> result >= RectangleValue(k, m, b)
  ensures exists k :: ValidRectangleCorner(k, m, b) && result == RectangleValue(k, m, b)
// </vc-spec>
// <vc-code>
var max: int := -1;
  var best_k: int := -1;
  var k: int := 0;
  while k <= b
    invariant 0 <= k <= b + 1
    invariant max >= -1
    invariant forall k' :: 0 <= k' < k ==> max >= RectangleValue(k', m, b)
    invariant if best_k != -1 then 0 <= best_k < k && max == RectangleValue(best_k, m, b)
  {
    var x := k * m;
    var y := b - k;
    var val := f(x, y);
    if val > max {
      max := val;
      best_k := k;
    }
    k := k + 1;
  }
  result := max;
// </vc-code>

