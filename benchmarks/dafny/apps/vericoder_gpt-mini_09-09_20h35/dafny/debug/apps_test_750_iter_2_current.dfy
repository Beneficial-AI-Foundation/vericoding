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

  // CeilDiv(a,k) = qa + ia for non-negative a
  assert CeilDiv(a, k) == qa + ia;
  assert CeilDiv(b, k) == qb + ib;

  var s := ra + rb;
  // decompose s into carry and remainder: s = k * carry + rem
  var carry := s / k;
  var rem := s % k;
  assert s == k * carry + rem;
  assert 0 <= rem < k;

  // express CeilDiv(a+b,k) in terms of qa,qb and s
  // For s == 0 -> extra = 0
  // For 1 <= s <= k-1 -> extra = 1
  // For k <= s <= 2k-2 -> extra = 2
  var extra := (if s == 0 then 0 else 1) + (if s >= k then 1 else 0);
  assert CeilDiv(a + b, k) == qa + qb + extra;

  // Now show ia + ib >= extra by cases on s
  if s == 0 {
    // then ra==0 and rb==0, so ia+ib == 0
    assert ia + ib == 0;
    assert ia + ib >= extra;
  } else if s < k {
    // then at least one of ra,rb is > 0, so ia+ib >= 1 and extra == 1
    assert ia + ib >= 1;
    assert extra == 1;
    assert ia + ib >= extra;
  } else {
    // s >= k, since 0 <= ra,rb < k, both ra and rb must be > 0, so ia+ib == 2 and extra == 2
    assert ia + ib == 2;
    assert extra == 2;
    assert ia + ib >= extra;
  }

  // conclude
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

