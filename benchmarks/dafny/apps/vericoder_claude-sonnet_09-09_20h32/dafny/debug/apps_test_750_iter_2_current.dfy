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
  (a + b - 1) / b
}

lemma CeilDivNonNegative(a: int, b: int)
  requires a >= 0 && b > 0
  ensures CeilDiv(a, b) >= 0
{
}

lemma CeilDivSum(a: int, b: int, c: int, k: int)
  requires a >= 0 && b >= 0 && c >= 0 && k > 0
  ensures CeilDiv(a, k) + CeilDiv(b, k) + CeilDiv(c, k) >= CeilDiv(a + b + c, k)
{
  var sum := a + b + c;
  var ceil_a := CeilDiv(a, k);
  var ceil_b := CeilDiv(b, k);
  var ceil_c := CeilDiv(c, k);
  var ceil_sum := CeilDiv(sum, k);
  
  assert ceil_a * k >= a;
  assert ceil_b * k >= b;
  assert ceil_c * k >= c;
  assert (ceil_a + ceil_b + ceil_c) * k >= sum;
  
  if (ceil_a + ceil_b + ceil_c) * k - k < sum {
    assert ceil_a + ceil_b + ceil_c >= ceil_sum;
  } else {
    assert ceil_a + ceil_b + ceil_c >= ceil_sum;
  }
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
  var sheets1 := CeilDiv(2 * n, k);
  var sheets2 := CeilDiv(5 * n, k);
  var sheets3 := CeilDiv(8 * n, k);
  result := sheets1 + sheets2 + sheets3;
  
  CeilDivNonNegative(2 * n, k);
  CeilDivNonNegative(5 * n, k);
  CeilDivNonNegative(8 * n, k);
  
  assert TotalSheetsNeeded(n) == 2 * n + 5 * n + 8 * n;
  CeilDivSum(2 * n, 5 * n, 8 * n, k);
}
// </vc-code>

