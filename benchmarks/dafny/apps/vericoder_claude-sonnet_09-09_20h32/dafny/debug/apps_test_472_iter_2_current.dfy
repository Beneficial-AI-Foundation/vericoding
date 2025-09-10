function digitSum(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else (n % 10) + digitSum(n / 10)
}

// <vc-helpers>
function f(x: int): int
  requires x > 0
{
  x * x + digitSum(x) * x
}

lemma DigitSumNonnegative(x: int)
  requires x >= 0
  ensures digitSum(x) >= 0
{
  if x == 0 {
  } else {
    DigitSumNonnegative(x / 10);
  }
}

lemma FunctionGrowth(x: int)
  requires x > 0
  ensures f(x) >= x
{
  DigitSumNonnegative(x);
  assert digitSum(x) >= 0;
  assert f(x) == x * x + digitSum(x) * x == x * (x + digitSum(x));
  assert x + digitSum(x) >= x;
  assert f(x) >= x * x;
  assert f(x) >= x;
}

lemma FunctionMonotonic(x: int, y: int)
  requires x > 0 && y > 0
  requires x < y
  ensures f(x) < f(y)
{
  DigitSumNonnegative(x);
  DigitSumNonnegative(y);
  assert f(x) == x * x + digitSum(x) * x;
  assert f(y) == y * y + digitSum(y) * y;
  assert x * x < y * y;
  assert digitSum(x) * x >= 0 && digitSum(y) * y >= 0;
  assert f(x) <= x * x + digitSum(x) * x < y * y <= y * y + digitSum(y) * y == f(y);
}

lemma FunctionBound(x: int)
  requires x > 0
  ensures f(x) <= x * x + 9 * (x - 1) * x / 1 + x
{
  DigitSumNonnegative(x);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires n >= 1
  ensures n == 1 ==> result == -1
  ensures n > 1 && result > 0 ==> result * result + digitSum(result) * result == n
  ensures n > 1 && result > 0 ==> forall y :: y > 0 && y < result ==> y * y + digitSum(y) * y != n
  ensures n > 1 && result == -1 ==> forall x :: x > 0 ==> x * x + digitSum(x) * x != n
  ensures result == -1 || result > 0
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    return -1;
  }
  
  var x := 1;
  var bound := n;
  FunctionGrowth(1);
  
  while x <= bound
    invariant x >= 1
    invariant forall y :: 1 <= y < x ==> f(y) != n
    invariant bound >= 1
    invariant x <= bound + 1
    decreases bound - x + 1
  {
    var fx := x * x + digitSum(x) * x;
    if fx == n {
      return x;
    }
    if fx > n {
      return -1;
    }
    x := x + 1;
  }
  
  return -1;
}
// </vc-code>

