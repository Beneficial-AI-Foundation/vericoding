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
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(m: int, b: int) returns (result: int)
  requires ValidInput(m, b)
  ensures result >= -1
  ensures forall k :: ValidRectangleCorner(k, m, b) ==> result >= RectangleValue(k, m, b)
  ensures exists k :: ValidRectangleCorner(k, m, b) && result == RectangleValue(k, m, b)
// </vc-spec>
// <vc-code>
{
  var maxVal := -1;
  for k := 0 to b+1
    invariant 0 <= k <= b+1
    invariant maxVal >= -1
    invariant maxVal == -1 <==> k == 0
    invariant maxVal != -1 ==> exists j :: 0 <= j < k && ValidRectangleCorner(j, m, b) && maxVal == RectangleValue(j, m, b)
    invariant forall i :: ValidRectangleCorner(i, m, b) && i < k ==> maxVal >= RectangleValue(i, m, b)
  {
    if ValidRectangleCorner(k, m, b) {
      var current := RectangleValue(k, m, b);
      if current > maxVal {
        maxVal := current;
      }
    }
  }
  return maxVal;
}
// </vc-code>

