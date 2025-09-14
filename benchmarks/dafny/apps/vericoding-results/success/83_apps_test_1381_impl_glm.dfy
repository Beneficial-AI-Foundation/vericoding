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
lemma CeilingDivisionProperties(x: int, p: int)
  requires x >= 0 && p >= 1
  ensures (x + p - 1) / p * p >= x
  ensures ((x + p - 1) / p - 1) * p < x
{
  var q := x / p;
  var r := x % p;
  assert x == p * q + r && 0 <= r < p;
  
  if r == 0 {
    calc {
      (x + p - 1) / p;
      (p * q + p - 1) / p;
      q + (p - 1) / p;
      { assert (p - 1) / p == 0; }
      q;
    }
    assert (x + p - 1) / p * p == q * p == x;
    assert ((x + p - 1) / p - 1) * p == (q - 1) * p == p * q - p == x - p < x;
  } else {
    calc {
      (x + p - 1) / p;
      (p * q + r + p - 1) / p;
      q + (r + p - 1) / p;
    }
    assert r + p - 1 >= p;
    assert r + p - 1 < 2 * p;
    assert (r + p - 1) / p == 1;
    assert (x + p - 1) / p == q + 1;
    assert (x + p - 1) / p * p == (q + 1) * p == p * q + p > p * q + r == x;
    assert ((x + p - 1) / p - 1) * p == q * p < p * q + r == x;
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
  result := MinPacksNeeded(k, n, s, p);
}
// </vc-code>

