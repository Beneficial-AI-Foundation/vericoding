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
  var q := x / y;
  var rem := x % y;
  assert x == q * y + rem;
  assert 0 <= rem && rem < y;
  var c := (x + y - 1) / y;
  if rem == 0 {
    // x = q*y
    assert (y - 1) >= 0;
    assert (y - 1) < y;
    assert (y - 1) / y == 0;
    assert c == q;
    assert c * y >= x;
    assert (c - 1) * y < x;
  } else {
    // 1 <= rem <= y-1
    assert rem >= 1 && rem <= y - 1;
    assert rem + y - 1 >= y;
    assert rem + y - 1 < 2 * y;
    assert (rem + y - 1) / y == 1;
    assert c == q + 1;
    assert c * y >= x;
    assert (c - 1) * y < x;
  }
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

