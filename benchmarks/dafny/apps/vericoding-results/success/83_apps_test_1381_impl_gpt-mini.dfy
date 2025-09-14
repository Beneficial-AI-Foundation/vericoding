predicate ValidInput(k: int, n: int, s: int, p: int)
{
  k >= 1 && n >= 1 && s >= 1 && p >= 1 &&
  k <= 10000 && n <= 10000 && s <= 10000 && p <= 10000
}

function SheetsPerPerson(n: int, s: int): int
  requires s >= 1
{
  (n + s - 1) / s
}

function TotalSheetsNeeded(k: int, n: int, s: int): int
  requires s >= 1
{
  k * SheetsPerPerson(n, s)
}

function MinPacksNeeded(k: int, n: int, s: int, p: int): int
  requires s >= 1 && p >= 1
{
  (TotalSheetsNeeded(k, n, s) + p - 1) / p
}

predicate CorrectResult(result: int, k: int, n: int, s: int, p: int)
  requires s >= 1 && p >= 1
{
  result == MinPacksNeeded(k, n, s, p) &&
  result * p >= TotalSheetsNeeded(k, n, s) &&
  (result - 1) * p < TotalSheetsNeeded(k, n, s)
}

// <vc-helpers>
lemma CeilDivBounds(x: int, y: int)
  requires y > 0 && x >= 0
  ensures ((x + y - 1) / y) * y >= x
  ensures (((x + y - 1) / y) - 1) * y < x
{
  var a := x + y - 1;
  var q := a / y;
  var r := a % y;
  assert a == q * y + r;
  assert 0 <= r && r < y;
  // q * y = a - r >= x because r <= y-1
  assert r <= y - 1;
  assert q * y == a - r;
  assert a - r >= x;
  assert q * y >= x;
  // (q - 1) * y = a - r - y = x - 1 - r < x because r >= 0
  assert (q - 1) * y == a - r - y;
  assert a - r - y <= x - 1;
  assert (q - 1) * y < x;
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, n: int, s: int, p: int) returns (result: int)
  requires ValidInput(k, n, s, p)
  ensures result >= 1
  ensures CorrectResult(result, k, n, s, p)
// </vc-spec>
// <vc-code>
{
  var total := TotalSheetsNeeded(k, n, s);
  result := MinPacksNeeded(k, n, s, p);
  CeilDivBounds(total, p);
  assert result * p >= total;
  assert (result - 1) * p < total;
  assert result >= 1;
}
// </vc-code>

