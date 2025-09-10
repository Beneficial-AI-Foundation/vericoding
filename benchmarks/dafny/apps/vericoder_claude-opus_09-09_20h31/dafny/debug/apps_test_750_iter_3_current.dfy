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
  requires a >= 0
{
  (a + b - 1) / b
}

lemma CeilDivCorrect(a: int, b: int)
  requires b > 0
  requires a >= 0
  ensures CeilDiv(a, b) * b >= a
  ensures CeilDiv(a, b) >= a / b
{
}

lemma CeilDivNonNegative(a: int, b: int)
  requires b > 0
  requires a >= 0
  ensures CeilDiv(a, b) >= 0
{
}

lemma CeilDivSum(n: int, k: int)
  requires n >= 1 && k >= 1
  ensures CeilDiv(2 * n, k) + CeilDiv(5 * n, k) + CeilDiv(8 * n, k) >= CeilDiv(15 * n, k)
  ensures CeilDiv(15 * n, k) == (TotalSheetsNeeded(n) + k - 1) / k
{
  assert TotalSheetsNeeded(n) == 15 * n;
  
  // Help the verifier by establishing the relationship step by step
  var sum := CeilDiv(2 * n, k) + CeilDiv(5 * n, k) + CeilDiv(8 * n, k);
  
  // Use the fact that ceiling of sum is at most sum of ceilings
  CeilDivCorrect(2 * n, k);
  CeilDivCorrect(5 * n, k);
  CeilDivCorrect(8 * n, k);
  
  assert sum * k >= CeilDiv(2 * n, k) * k + CeilDiv(5 * n, k) * k + CeilDiv(8 * n, k) * k;
  assert CeilDiv(2 * n, k) * k >= 2 * n;
  assert CeilDiv(5 * n, k) * k >= 5 * n;
  assert CeilDiv(8 * n, k) * k >= 8 * n;
  assert sum * k >= 2 * n + 5 * n + 8 * n;
  assert sum * k >= 15 * n;
  
  // Therefore sum >= CeilDiv(15 * n, k)
  assert sum >= (15 * n + k - 1) / k;
  assert CeilDiv(15 * n, k) == (15 * n + k - 1) / k;
  assert CeilDiv(15 * n, k) == (TotalSheetsNeeded(n) + k - 1) / k;
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
  var red := CeilDiv(2 * n, k);
  var green := CeilDiv(5 * n, k);
  var blue := CeilDiv(8 * n, k);
  
  CeilDivNonNegative(2 * n, k);
  CeilDivNonNegative(5 * n, k);
  CeilDivNonNegative(8 * n, k);
  
  CeilDivSum(n, k);
  
  result := red + green + blue;
}
// </vc-code>

