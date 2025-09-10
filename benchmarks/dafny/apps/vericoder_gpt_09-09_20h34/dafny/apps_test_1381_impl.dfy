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
lemma CeilDivBounds(a: int, d: int)
  requires a >= 1
  requires d >= 1
  ensures ((a + d - 1) / d) * d >= a
  ensures (((a + d - 1) / d) - 1) * d < a
  ensures ((a + d - 1) / d) >= 1
{
  var x := a + d - 1;
  var q := x / d;
  var r := x % d;
  assert x == q * d + r;
  assert 0 <= r;
  assert r < d;
  assert r <= d - 1;
  assert q * d >= x - (d - 1);
  assert x - (d - 1) == a;
  assert q * d >= a;
  assert (q - 1) * d == q * d - d;
  assert q * d == x - r;
  assert (q - 1) * d == (x - r) - d;
  assert (q - 1) * d <= (x - d) - 0;
  assert x - d == a - 1;
  assert (q - 1) * d <= a - 1;
  assert (q - 1) * d < a;
  assert a - 1 >= 0;
  assert x >= d;
  if q == 0 {
    assert x == r;
    assert x < d;
    assert false;
  }
  assert q >= 1;
  assert ((a + d - 1) / d) == q;
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
  result := (total + p - 1) / p;
  ghost call CeilDivBounds(total, p);
  assert result == (total + p - 1) / p;
  assert result >= 1;
  assert result * p >= total;
  assert (result - 1) * p < total;
  assert result == MinPacksNeeded(k, n, s, p);
}
// </vc-code>

