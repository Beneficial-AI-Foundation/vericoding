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

  assert 0 < k;
  assert k * CeilDiv(2 * n, k) >= 2 * n;
  assert k * CeilDiv(5 * n, k) >= 5 * n;
  assert k * CeilDiv(8 * n, k) >= 8 * n;

  assert k * result >= TotalSheetsNeeded(n);
  assert (TotalSheetsNeeded(n) + k - 1) / k <= (k * result + k - 1) / k;

  assert 0 <= k - 1 < k;
  assert (k * result + k - 1) / k == result;
}
// </vc-code>

