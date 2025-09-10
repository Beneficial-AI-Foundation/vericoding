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
  if a == 0 then 0
  else (a - 1) / b + 1
}

lemma CeilDivLemma(a: int, b: int)
  requires b > 0
  ensures CeilDiv(a, b) == (a + b - 1) / b
{
  if a > 0 {
    // For positive a, both definitions are equivalent
    // (a + b - 1)/b = (a - 1)/b + 1 when a > 0
    assert (a + b - 1) / b == (a - 1) / b + 1;
  } else {
    // For non-positive a, both return 0
    assert a <= 0 ==> (a + b - 1) / b <= 0;
  }
}

lemma CeilDivAddLemma(a: int, b: int, c: int, k: int)
  requires k > 0
  ensures CeilDiv(a, k) + CeilDiv(b, k) + CeilDiv(c, k) >= CeilDiv(a + b + c, k)
{
  // The equality doesn't always hold (e.g., a=1,b=1,c=1,k=2)
  // But we only need the inequality for our postcondition
  // CeilDiv(a+b+c) <= CeilDiv(a) + CeilDiv(b) + CeilDiv(c)
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
  result := CeilDiv(2 * n, k) + CeilDiv(5 * n, k) + CeilDiv(8 * n, k);
}
// </vc-code>

