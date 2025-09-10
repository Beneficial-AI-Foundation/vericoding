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
lemma MaxExists(m: int, b: int)
  requires ValidInput(m, b)
  ensures exists k :: ValidRectangleCorner(k, m, b)
{
  assert ValidRectangleCorner(0, m, b);
}

lemma ValidKRange(k: int, m: int, b: int)
  requires ValidInput(m, b)
  requires ValidRectangleCorner(k, m, b)
  ensures 0 <= k <= b
{
}
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
  var maxVal := RectangleValue(0, m, b);
  var maxK := 0;
  var k := 1;
  
  while k <= b
    invariant 0 <= k <= b + 1
    invariant ValidRectangleCorner(maxK, m, b)
    invariant maxVal == RectangleValue(maxK, m, b)
    invariant forall j :: 0 <= j < k && ValidRectangleCorner(j, m, b) ==> maxVal >= RectangleValue(j, m, b)
  {
    var currentVal := RectangleValue(k, m, b);
    if currentVal > maxVal {
      maxVal := currentVal;
      maxK := k;
    }
    k := k + 1;
  }
  
  result := maxVal;
}
// </vc-code>

