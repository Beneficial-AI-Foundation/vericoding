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

lemma CeilDiv_add_ge(a: int, b: int, k: int)
  requires k > 0 && a >= 0 && b >= 0
  ensures CeilDiv(a, k) + CeilDiv(b, k) >= CeilDiv(a + b, k)
{
  var qa := a / k;
  var ra := a % k;
  assert a == k * qa + ra;
  assert 0 <= ra < k;

  var qb := b / k;
  var rb := b % k;
  assert b == k * qb + rb;
  assert 0 <= rb < k;

  var ia := if ra == 0 then 0 else 1;
  var ib := if rb == 0 then 0 else 1;

  assert CeilDiv(a, k) == qa + ia;
  assert CeilDiv(b, k) == qb + ib;

  var s := ra + rb;
  assert a + b == k * (qa + qb) + s;

  // CeilDiv(a+b,k) = qa + qb + CeilDiv(s,k)
  assert CeilDiv(a + b, k) == qa + qb + CeilDiv(s, k);

  if ra == 0 && rb == 0 {
    // both zero remainders
    assert ia + ib == 0;
    assert s == 0;
    assert CeilDiv(s, k) == 0;
    assert ia + ib >= CeilDiv(s, k);
  } else if ra == 0 || rb == 0 {
    // exactly one remainder is non-zero and < k
    assert ia + ib == 1;
    assert 0 < s < k;
    assert CeilDiv(s, k) == 1;
    assert ia + ib >= CeilDiv(s, k);
  } else {
    // both remainders are non-zero
    assert ia + ib == 2;
    assert 0 < ra < k && 0 < rb < k;
    assert 0 < s <= 2 * k - 2;
    // hence CeilDiv(s,k) <= 2
    assert s + k - 1 < 3 * k;
    assert CeilDiv(s, k) <= 2;
    assert ia + ib >= CeilDiv(s, k);
  }

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

