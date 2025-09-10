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
  ensures b * CeilDiv(a,b) >= a
  ensures b * (CeilDiv(a,b) - 1) < a || a <= 0
{
  (a + b - 1) / b
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
  var s2n := 2 * n;
  var s5n := 5 * n;
  var s8n := 8 * n;

  result := CeilDiv(s2n, k) + CeilDiv(s5n, k) + CeilDiv(s8n, k);
}
// </vc-code>

