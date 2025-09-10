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
  requires a >= 0 && b > 0
{
  (a + b - 1) / b
}

lemma CeilDiv_Properties()
  ensures forall a: int, b: int :: a >= 0 && b > 0 ==> CeilDiv(a, b) >= 0
  ensures forall a: int, b: int :: a >= 0 && b > 0 ==> CeilDiv(a, b) * b >= a
  ensures forall a: int, b: int :: a >= 0 && b > 0 ==> CeilDiv(a, b) * b <= a + b - 1
  ensures forall n: int, k: int :: n >= 1 && k >= 1 ==> CeilDiv(2 * n, k) + CeilDiv(5 * n, k) + CeilDiv(8 * n, k) >= CeilDiv(15 * n, k)
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

