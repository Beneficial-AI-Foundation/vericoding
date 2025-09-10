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
lemma MaxValueExists(m: int, b: int)
  requires ValidInput(m, b)
  ensures exists k :: ValidRectangleCorner(k, m, b)
{
  assert ValidRectangleCorner(0, m, b);
}

lemma IterationMaintainsMax(m: int, b: int, i: int, currentMax: int, maxK: int)
  requires ValidInput(m, b)
  requires 0 <= i <= b + 1
  requires ValidRectangleCorner(maxK, m, b)
  requires currentMax == RectangleValue(maxK, m, b)
  requires forall k :: 0 <= k < i && ValidRectangleCorner(k, m, b) ==> currentMax >= RectangleValue(k, m, b)
  ensures forall k :: ValidRectangleCorner(k, m, b) ==> currentMax >= RectangleValue(k, m, b) || i <= b
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
  var maxValue := RectangleValue(0, m, b);
  var maxK := 0;
  var i := 1;
  
  while i <= b
    invariant 0 <= i <= b + 1
    invariant ValidRectangleCorner(maxK, m, b)
    invariant maxValue == RectangleValue(maxK, m, b)
    invariant forall k :: 0 <= k < i && ValidRectangleCorner(k, m, b) ==> maxValue >= RectangleValue(k, m, b)
  {
    if ValidRectangleCorner(i, m, b) {
      var currentValue := RectangleValue(i, m, b);
      if currentValue > maxValue {
        maxValue := currentValue;
        maxK := i;
      }
    }
    i := i + 1;
  }
  
  result := maxValue;
}
// </vc-code>

