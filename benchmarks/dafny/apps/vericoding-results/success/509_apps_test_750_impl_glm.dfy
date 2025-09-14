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
function CeilDiv(a: int, k: int): int
  requires k > 0
  requires a >= 0
  ensures CeilDiv(a, k) == (a + k - 1) / k
  ensures CeilDiv(a, k) * k >= a
  ensures CeilDiv(a, k) * k < a + k
{
  (a + k - 1) / k
}

lemma CeilDivSum(a: int, b: int, k: int)
  requires a >= 0 && b >= 0 && k > 0
  ensures CeilDiv(a, k) + CeilDiv(b, k) >= CeilDiv(a+b, k)
{
  var x := CeilDiv(a, k) + CeilDiv(b, k);
  assert x * k == (CeilDiv(a, k) * k) + (CeilDiv(b, k) * k);
  assert x * k >= a + b;

  if CeilDiv(a+b, k) > x {
    calc {
      (x+1)*k;
      <= // Since CeilDiv(a+b,k) >= x+1 and k>0
      CeilDiv(a+b, k)*k;
      <  // By the third postcondition of CeilDiv
      a+b+k;
    }
    // Thus: (x+1)*k < a+b+k  => x*k < a+b
    assert x*k < a+b;
    // But we have x*k >= a+b -> contradiction
    assert false;
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
  CeilDivSum(2*n, 5*n, k);
  CeilDivSum(7*n, 8*n, k);
  return CeilDiv(2*n, k) + CeilDiv(5*n, k) + CeilDiv(8*n, k);
}
// </vc-code>

