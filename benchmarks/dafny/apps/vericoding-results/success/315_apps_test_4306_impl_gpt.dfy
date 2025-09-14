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
lemma MinLeBoth(x: int, y: int)
  ensures min(x, y) <= x
  ensures min(x, y) <= y
{
  if x < y {
    assert min(x, y) == x;
    assert min(x, y) <= x;
    assert x <= y;
    assert min(x, y) <= y;
  } else {
    assert min(x, y) == y;
    assert min(x, y) <= y;
    assert y <= x; // since !(x < y) implies x >= y
    assert min(x, y) <= x;
  }
}

lemma MaxGeBoth(x: int, y: int)
  ensures max(x, y) >= x
  ensures max(x, y) >= y
{
  if x > y {
    assert max(x, y) == x;
    assert max(x, y) >= x;
    assert x >= y;
    assert max(x, y) >= y;
  } else {
    assert max(x, y) == y;
    assert max(x, y) >= y;
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
  result := IntervalOverlapLength(a, b, c, d);

  if min(b, d) - max(a, c) > 0 {
    assert result == min(b, d) - max(a, c);

    // Show min(b, d) <= 100 from ValidInput
    if b < d {
      assert min(b, d) == b;
      assert min(b, d) <= 100;
    } else {
      assert min(b, d) == d;
      assert min(b, d) <= 100;
    }

    // Show 0 <= max(a, c) from ValidInput
    if a > c {
      assert max(a, c) == a;
      assert 0 <= max(a, c);
    } else {
      assert max(a, c) == c;
      assert 0 <= max(a, c);
    }

    assert min(b, d) - max(a, c) <= min(b, d) - 0;
    assert min(b, d) - 0 == min(b, d);
    assert result <= min(b, d);
    assert result <= 100;
    assert result >= 0;
  } else {
    assert result == 0;
    assert result >= 0;
    assert result <= 100;
  }
}
// </vc-code>

