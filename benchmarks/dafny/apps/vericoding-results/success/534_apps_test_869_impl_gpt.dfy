predicate ValidInput(a: int, b: int)
{
  a >= 1 && b >= 1
}

function MaxDifferentDays(a: int, b: int): int
{
  if a < b then a else b
}

function RemainingAfterDifferent(a: int, b: int): int
{
  if a > b then a - MaxDifferentDays(a, b) else b - MaxDifferentDays(a, b)
}

function SameDays(a: int, b: int): int
{
  RemainingAfterDifferent(a, b) / 2
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (days_different: int, days_same: int)
  requires ValidInput(a, b)
  ensures days_different == MaxDifferentDays(a, b)
  ensures days_same == SameDays(a, b)
  ensures days_different >= 0
  ensures days_same >= 0
  ensures days_different <= a && days_different <= b
// </vc-spec>
// <vc-code>
{
  days_different := MaxDifferentDays(a, b);
  days_same := SameDays(a, b);

  // Prove bounds for days_different
  if a < b {
    assert days_different == a;
    assert days_different <= a;
    assert days_different <= b;
  } else {
    assert days_different == b;
    assert days_different <= a;
    assert days_different <= b;
  }
  assert days_different >= 0;

  // Prove non-negativity for days_same
  var rem := RemainingAfterDifferent(a, b);
  if a > b {
    assert rem == a - MaxDifferentDays(a, b);
    assert MaxDifferentDays(a, b) == b;
    assert rem == a - b;
    assert rem >= 0;
  } else {
    assert rem == b - MaxDifferentDays(a, b);
    if a < b {
      assert MaxDifferentDays(a, b) == a;
      assert rem == b - a;
      assert rem >= 0;
    } else {
      assert a == b;
      assert MaxDifferentDays(a, b) == b;
      assert rem == b - b;
      assert rem >= 0;
    }
  }
  assert days_same == rem / 2;
  assert days_same >= 0;
}
// </vc-code>

