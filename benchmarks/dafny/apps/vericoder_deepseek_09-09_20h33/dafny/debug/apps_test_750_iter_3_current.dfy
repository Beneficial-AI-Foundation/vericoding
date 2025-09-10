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
  if a <= 0 then 0
  else (a + b - 1) / b
}

lemma CeilDivLemma(a: int, b: int)
  requires b > 0
  ensures CeilDiv(a, b) == (a + b - 1) / b
{
}

lemma CeilDivAddLemma(a: int, b: int, c: int, k: int)
  requires k > 0
  ensures CeilDiv(a, k) + CeilDiv(b, k) + CeilDiv(c, k) == CeilDiv(a + b + c, k)
{
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
  result := CeilDiv(2 * n + 5 * n + 8 * n, k);
}
// </vc-code>

