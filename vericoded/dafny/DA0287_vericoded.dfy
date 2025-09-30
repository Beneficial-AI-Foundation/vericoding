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
  ensures (a + b - 1) / b >= a / b
  ensures (a + b - 1) / b * b >= a
{
  // Dafny can verify this automatically
}

lemma MinPacksCorrectness(k: int, n: int, s: int, p: int)
  requires ValidInput(k, n, s, p)
  ensures MinPacksNeeded(k, n, s, p) >= 1
  ensures MinPacksNeeded(k, n, s, p) * p >= TotalSheetsNeeded(k, n, s)
  ensures (MinPacksNeeded(k, n, s, p) - 1) * p < TotalSheetsNeeded(k, n, s)
{
  var total := TotalSheetsNeeded(k, n, s);
  var result := MinPacksNeeded(k, n, s, p);
  
  // result >= 1
  assert k >= 1 && SheetsPerPerson(n, s) >= 1;
  assert total >= 1;
  assert result == (total + p - 1) / p;
  assert result >= total / p;
  assert total >= 1 && p >= 1;
  assert result >= 1;
  
  // result * p >= total
  CeilingDivisionProperty(total, p);
  
  // (result - 1) * p < total
  assert result == (total + p - 1) / p;
  // By definition of ceiling division
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
  var sheets_per_person := (n + s - 1) / s;
  var total_sheets := k * sheets_per_person;
  result := (total_sheets + p - 1) / p;
  
  MinPacksCorrectness(k, n, s, p);
}
// </vc-code>

