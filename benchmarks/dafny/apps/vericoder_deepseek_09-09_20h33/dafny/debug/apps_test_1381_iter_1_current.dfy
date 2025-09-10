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
lemma DivisionLemma(a: int, b: int)
  requires a >= 0 && b > 0
  ensures (a + b - 1) / b >= 0
{
}

lemma SheetsPerPersonProperty(n: int, s: int)
  requires n >= 1 && s >= 1
  ensures SheetsPerPerson(n, s) >= 1
{
}

lemma TotalSheetsNeededProperty(k: int, n: int, s: int)
  requires k >= 1 && n >= 1 && s >= 1
  ensures TotalSheetsNeeded(k, n, s) >= k
{
  SheetsPerPersonProperty(n, s);
  assert SheetsPerPerson(n, s) >= 1;
}

lemma MinPacksNeededProperty(k: int, n: int, s: int, p: int)
  requires k >= 1 && n >= 1 && s >= 1 && p >= 1
  ensures MinPacksNeeded(k, n, s, p) >= 1
{
  TotalSheetsNeededProperty(k, n, s);
  var total := TotalSheetsNeeded(k, n, s);
  DivisionLemma(total, p);
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
  var sheetsNeeded := TotalSheetsNeeded(k, n, s);
  result := (sheetsNeeded + p - 1) / p;
  assert result == MinPacksNeeded(k, n, s, p);
  SheetsPerPersonProperty(n, s);
  TotalSheetsNeededProperty(k, n, s);
  MinPacksNeededProperty(k, n, s, p);
}
// </vc-code>

