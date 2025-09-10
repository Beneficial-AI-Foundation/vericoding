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
lemma CeilingDivisionProperty(a: int, b: int)
  requires a >= 0 && b >= 1
  ensures (a + b - 1) / b * b >= a
  ensures (a + b - 1) / b == 0 ==> a == 0
  ensures a > 0 ==> ((a + b - 1) / b - 1) * b < a
{
  if a == 0 {
    assert (a + b - 1) / b == (b - 1) / b == 0;
  } else {
    var ceil_div := (a + b - 1) / b;
    assert ceil_div >= 1;
    assert ceil_div * b >= a;
    assert (ceil_div - 1) * b < a;
  }
}

lemma SheetsPerPersonCorrect(n: int, s: int)
  requires n >= 1 && s >= 1
  ensures SheetsPerPerson(n, s) >= 1
  ensures SheetsPerPerson(n, s) * s >= n
  ensures (SheetsPerPerson(n, s) - 1) * s < n
{
  CeilingDivisionProperty(n, s);
}

lemma MinPacksNeededCorrect(k: int, n: int, s: int, p: int)
  requires k >= 1 && n >= 1 && s >= 1 && p >= 1
  ensures MinPacksNeeded(k, n, s, p) >= 1
  ensures MinPacksNeeded(k, n, s, p) * p >= TotalSheetsNeeded(k, n, s)
  ensures (MinPacksNeeded(k, n, s, p) - 1) * p < TotalSheetsNeeded(k, n, s)
{
  var total := TotalSheetsNeeded(k, n, s);
  SheetsPerPersonCorrect(n, s);
  assert total >= k;
  CeilingDivisionProperty(total, p);
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
  var sheetsPerPerson := (n + s - 1) / s;
  var totalSheets := k * sheetsPerPerson;
  result := (totalSheets + p - 1) / p;
  
  SheetsPerPersonCorrect(n, s);
  MinPacksNeededCorrect(k, n, s, p);
  
  assert sheetsPerPerson == SheetsPerPerson(n, s);
  assert totalSheets == TotalSheetsNeeded(k, n, s);
  assert result == MinPacksNeeded(k, n, s, p);
}
// </vc-code>

