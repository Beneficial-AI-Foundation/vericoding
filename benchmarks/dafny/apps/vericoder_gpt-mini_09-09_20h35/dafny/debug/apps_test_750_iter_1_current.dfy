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
  requires k > 0
  ensures CeilDiv(a, k) + CeilDiv(b, k) >= CeilDiv(a + b, k)
{
  calc {
    CeilDiv(a, k) + CeilDiv(b, k);
    == (a + k - 1) / k + (b + k - 1) / k;
    == (a + b + 2 * k - 2) / k;
    >= (a + b + k - 1) / k;
    == CeilDiv(a + b, k);
  }
}

lemma CeilDiv_three_ge(a: int, b: int, c: int, k: int)
  requires k > 0
  ensures CeilDiv(a, k) + CeilDiv(b, k) + CeilDiv(c, k) >= CeilDiv(a + b + c, k)
{
  CeilDiv_add_ge(a, b, k);
  // from CeilDiv_add_ge: CeilDiv(a,k)+CeilDiv(b,k) >= CeilDiv(a+b,k)
  assert CeilDiv(a, k) + CeilDiv(b, k) + CeilDiv(c, k) >= CeilDiv(a + b, k) + CeilDiv(c, k);
  CeilDiv_add_ge(a + b, c, k);
  // from CeilDiv_add_ge: CeilDiv(a+b,k)+CeilDiv(c,k) >= CeilDiv(a+b+c,k)
  assert CeilDiv(a, k) + CeilDiv(b, k) + CeilDiv(c, k) >= CeilDiv(a + b + c, k);
}

lemma CeilDiv_nonneg(a: int, k: int)
  requires k > 0 && a >= 0
  ensures CeilDiv(a, k) >= 0
{
  // CeilDiv(a,k) = (a + k - 1)/k and a + k - 1 >= 0 when a >= 0 and k >= 1
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

