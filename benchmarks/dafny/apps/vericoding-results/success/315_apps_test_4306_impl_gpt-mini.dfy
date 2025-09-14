predicate ValidInput(a: int, b: int, c: int, d: int)
{
    0 <= a < b <= 100 && 0 <= c < d <= 100
}

function min(x: int, y: int): int
{
    if x < y then x else y
}

function max(x: int, y: int): int
{
    if x > y then x else y
}

function IntervalOverlapLength(a: int, b: int, c: int, d: int): int
{
    if min(b, d) - max(a, c) > 0 then min(b, d) - max(a, c) else 0
}

// <vc-helpers>
lemma MinLeLeft(x:int, y:int)
  ensures min(x, y) <= x
{
  if x < y {
    assert min(x, y) == x;
    assert min(x, y) <= x;
  } else {
    // x >= y
    assert min(x, y) == y;
    assert y <= x;
    assert min(x, y) <= x;
  }
}

lemma MaxGeLeft(x:int, y:int)
  ensures max(x, y) >= x
{
  if x > y {
    assert max(x, y) == x;
    assert max(x, y) >= x;
  } else {
    // x <= y
    assert max(x, y) == y;
    assert y >= x;
    assert max(x, y) >= x;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int) returns (result: int)
    requires ValidInput(a, b, c, d)
    ensures result >= 0
    ensures result == IntervalOverlapLength(a, b, c, d)
    ensures result <= 100
// </vc-spec>
// <vc-code>
{
  var lo := max(a, c);
  var hi := min(b, d);
  if hi - lo > 0 {
    result := hi - lo;

    // prove result <= 100
    MinLeLeft(b, d);
    assert hi <= b;
    assert b <= 100;
    assert hi <= 100;

    MaxGeLeft(a, c);
    assert lo >= a;
    assert a >= 0;
    assert lo >= 0;

    assert result <= 100;
  } else {
    result := 0;
    assert result <= 100;
  }

  // prove result matches the specification
  assert result == IntervalOverlapLength(a, b, c, d);
  assert result >= 0;
}
// </vc-code>

