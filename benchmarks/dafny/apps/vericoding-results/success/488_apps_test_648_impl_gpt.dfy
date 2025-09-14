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
lemma f_nonneg(x: int, y: int)
  requires x >= 0 && y >= 0
  ensures f(x, y) >= 0
{
  assert x + 1 >= 0;
  assert y + 1 >= 0;

  assert x * (x + 1) >= 0;
  assert (x * (x + 1)) * (y + 1) >= 0;

  assert y * (y + 1) >= 0;
  assert (y * (y + 1)) * (x + 1) >= 0;

  assert x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1) >= 0;
  assert f(x, y) == (x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2;
  assert (x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2 >= 0;
}

lemma RectangleValueNonNeg(k: int, m: int, b: int)
  requires ValidRectangleCorner(k, m, b)
  requires m >= 1
  ensures RectangleValue(k, m, b) >= 0
{
  var x := k * m;
  var y := b - k;
  assert x >= 0;
  assert y >= 0;
  f_nonneg(x, y);
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
  var i := 0;
  var bestK := 0;
  assert ValidRectangleCorner(0, m, b);
  var best := RectangleValue(0, m, b);
  RectangleValueNonNeg(0, m, b);
  assert best >= 0;
  i := 1;
  while i <= b
    invariant 1 <= i <= b + 1
    invariant ValidRectangleCorner(bestK, m, b)
    invariant best == RectangleValue(bestK, m, b)
    invariant forall k :: 0 <= k < i ==> best >= RectangleValue(k, m, b)
    invariant best >= -1
    decreases b - i + 1
  {
    assert ValidRectangleCorner(i, m, b);
    var v := RectangleValue(i, m, b);
    RectangleValueNonNeg(i, m, b);
    assert v >= 0;
    if v > best {
      best := v;
      bestK := i;
    }
    i := i + 1;
  }
  assert i == b + 1;
  assert forall k :: ValidRectangleCorner(k, m, b) ==> 0 <= k < i;
  assert forall k :: ValidRectangleCorner(k, m, b) ==> best >= RectangleValue(k, m, b);
  assert exists k :: ValidRectangleCorner(k, m, b) && best == RectangleValue(k, m, b);
  result := best;
}
// </vc-code>

