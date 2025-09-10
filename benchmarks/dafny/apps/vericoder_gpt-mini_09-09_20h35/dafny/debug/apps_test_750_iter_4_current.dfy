predicate ValidInput(n: int, k: int)
{
  n >= 1 && k >= 1
}

function SheetsNeeded(n: int): (int, int, int)
{
  (2 * n, 5 * n, 8 * n)
}

function TotalSheetsNeeded(n: int): int
{
  2 * n + 5 * n + 8 * n
}

// <vc-helpers>
function CeilDiv(a: int, b: int): int
  requires b > 0
{
  (a + b - 1) / b
}

lemma CeilDiv_leq_two_when_less_than_2k(s: int, k: int)
  requires k > 0 && 0 <= s < 2 * k
  ensures CeilDiv(s, k) <= 2
{
  // CeilDiv(s,k) = (s + k - 1) / k
  // Since s < 2*k, s + k - 1 < 3*k, so (s + k - 1) / k <= 2
  assert s + k - 1 < 3 * k;
  assert CeilDiv(s, k) <= 2;
}

lemma CeilDiv_add_ge(a: int, b: int, k: int)
  requires k > 0 && a >= 0 && b >= 0
  ensures CeilDiv(a, k) + CeilDiv(b, k) >= CeilDiv(a + b, k)
{
  var qa := a / k;
  var ra := a % k;
  var qb := b / k;
  var rb := b % k;

  assert 0 <= ra < k;
  assert 0 <= rb < k;

  var ia := if ra == 0 then 0 else 1;
  var ib := if rb == 0 then 0 else 1;

  assert CeilDiv(a, k) == qa + ia;
  assert CeilDiv(b, k) == qb + ib;

  var s := ra + rb;
  assert CeilDiv(a + b, k) == qa + qb + CeilDiv(s, k);

  // Need to show ia + ib >= CeilDiv(s,k)
  if ia + ib == 0 {
    // both remainders zero
    assert s == 0;
    assert CeilDiv(s, k) == 0;
  } else if ia + ib == 1 {
    // exactly one remainder non-zero => 0 < s < k
    assert 0 < s < k;
    assert CeilDiv(s, k) == 1;
  } else {
    // ia + ib == 2 => both remainders non-zero
    assert 0 < ra < k && 0 < rb < k;
    // hence 1 <= s < 2*k
    assert 1 <= s < 2 * k;
    CeilDiv_leq_two_when_less_than_2k(s, k);
  }

  assert ia + ib >= CeilDiv(s, k);
  assert CeilDiv(a, k) + CeilDiv(b, k) >= CeilDiv(a + b, k);
}

lemma CeilDiv_three_ge(a: int, b: int, c: int, k: int)
  requires k > 0 && a >= 0 && b >= 0 && c >= 0
  ensures CeilDiv(a, k) + CeilDiv(b, k) + CeilDiv(c, k) >= CeilDiv(a + b + c, k)
{
  CeilDiv_add_ge(a, b, k);
  assert CeilDiv(a, k) + CeilDiv(b, k) + CeilDiv(c, k) >= CeilDiv(a + b, k) + CeilDiv(c, k);
  CeilDiv_add_ge(a + b, c, k);
  assert CeilDiv(a, k) + CeilDiv(b, k) + CeilDiv(c, k) >= CeilDiv(a + b + c, k);
}

lemma CeilDiv_nonneg(a: int, k: int)
  requires k > 0 && a >= 0
  ensures CeilDiv(a, k) >= 0
{
  assert a + k - 1 >= 0;
  assert CeilDiv(a, k) >= 0;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result == CeilDiv(2 * n, k) + CeilDiv(5 * n, k) + CeilDiv(8 * n, k)
  ensures result >= 0
  ensures result >= (TotalSheetsNeeded(n) + k - 1) / k
// </vc-spec>
// <vc-code>
{
  result := CeilDiv(2 * n, k) + CeilDiv(5 * n, k) + CeilDiv(8 * n, k);

  // prove non-negativity
  CeilDiv_nonneg(2 * n, k);
  CeilDiv_nonneg(5 * n, k);
  CeilDiv_nonneg(8 * n, k);
  assert result >= 0;

  // prove lower bound w.r.t total sheets
  CeilDiv_three_ge(2 * n, 5 * n, 8 * n, k);
  assert result >= CeilDiv(TotalSheetsNeeded(n), k);
  return;
}
// </vc-code>

