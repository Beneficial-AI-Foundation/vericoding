predicate ValidInput(k: int, a: int, b: int)
{
  k > 0 && a <= b
}

function FloorDiv(a: int, b: int): int
  requires b > 0
{
  if a >= 0 then a / b
  else (a - b + 1) / b
}

function CountDivisiblesInRange(k: int, a: int, b: int): int
  requires k > 0
  requires a <= b
{
  FloorDiv(b, k) - FloorDiv(a - 1, k)
}

// <vc-helpers>
lemma IntDiv_monotone(k: int, u: int, v: int)
  requires k > 0
  requires u <= v
  ensures u / k <= v / k
{
  var qu := u / k;
  var ru := u % k;
  var qv := v / k;
  var rv := v % k;

  // Division/remainder identities for positive divisor
  assert u == qu * k + ru;
  assert v == qv * k + rv;
  assert 0 <= ru && ru < k;
  assert 0 <= rv && rv < k;

  if !(qu <= qv) {
    // Assume qu > qv and derive contradiction.
    assert qu - qv >= 1;
    // From u <= v and the identities:
    assert qu * k + ru <= qv * k + rv;
    // Rearranging gives (qu - qv) * k <= rv - ru
    assert (qu - qv) * k <= rv - ru;
    // But rv - ru < k, so (qu - qv) * k < k
    assert rv - ru < k;
    assert (qu - qv) * k < k;
    // Since qu - qv >= 1 and k > 0, (qu - qv) * k >= k, contradiction
    assert (qu - qv) * k >= k;
    assert false;
  }
}

lemma FloorDiv_monotone(k: int, x: int, y: int)
  requires k > 0
  requires x <= y
  ensures FloorDiv(x, k) <= FloorDiv(y, k)
{
  if x >= 0 {
    // then y >= 0 as well because x <= y
    assert y >= 0;
    assert FloorDiv(x, k) == x / k;
    assert FloorDiv(y, k) == y / k;
    IntDiv_monotone(k, x, y);
  } else {
    if y < 0 {
      // both negative: FloorDiv uses (a - k + 1) / k which is monotone in a
      assert FloorDiv(x, k) == (x - k + 1) / k;
      assert FloorDiv(y, k) == (y - k + 1) / k;
      IntDiv_monotone(k, x - k + 1, y - k + 1);
    } else {
      // x < 0 <= y: compare (x - k + 1)/k to y/k
      assert FloorDiv(x, k) == (x - k + 1) / k;
      assert FloorDiv(y, k) == y / k;
      // x - k + 1 <= y holds because x <= y and -k+1 <= 0
      assert x - k + 1 <= y;
      IntDiv_monotone(k, x - k + 1, y);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, a: int, b: int) returns (result: int)
  requires ValidInput(k, a, b)
  ensures result >= 0
  ensures result == CountDivisiblesInRange(k, a, b)
// </vc-spec>
// <vc-code>
{
  result := CountDivisiblesInRange(k, a, b);
  CountDivisibles_nonneg(k, a, b);
}
// </vc-code>

