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

lemma DigitSumBound(x: int)
  requires x > 0
  ensures digitSum(x) <= 9 * x
{
  if x < 10 {
    assert digitSum(x) == x <= 9;
    assert 9 * x >= 9 >= x;
  } else {
    DigitSumBound(x / 10);
    assert digitSum(x) == (x % 10) + digitSum(x / 10);
    assert x % 10 <= 9;
    assert digitSum(x / 10) <= 9 * (x / 10);
    assert digitSum(x) <= 9 + 9 * (x / 10);
    assert 9 + 9 * (x / 10) == 9 * (1 + x / 10);
    assert 1 + x / 10 <= x;
    assert digitSum(x) <= 9 * x;
  }
}

lemma FunctionGrowth(x: int)
  requires x > 0
  ensures f(x) >= x
{
  DigitSumNonnegative(x);
  assert digitSum(x) >= 0;
  assert f(x) == x * x + digitSum(x) * x;
  assert f(x) >= x * x >= x;
}

lemma FunctionMonotonic(x: int, y: int)
  requires x > 0 && y > 0
  requires x < y
  ensures f(x) < f(y)
{
  DigitSumNonnegative(x);
  DigitSumNonnegative(y);
  DigitSumBound(x);
  DigitSumBound(y);
  
  assert f(x) == x * x + digitSum(x) * x;
  assert f(y) == y * y + digitSum(y) * y;
  assert x * x < y * y;
  
  assert digitSum(x) * x <= 9 * x * x;
  assert digitSum(y) * y <= 9 * y * y;
  
  assert f(x) <= x * x + 9 * x * x == 10 * x * x;
  assert f(y) >= y * y;
  
  assert y >= x + 1;
  assert y * y >= (x + 1) * (x + 1) == x * x + 2 * x + 1;
  assert x * x + 2 * x + 1 > 10 * x * x ==> f(y) > f(x);
  
  if x * x + 2 * x + 1 <= 10 * x * x {
    assert 2 * x + 1 <= 9 * x * x;
    assert f(x) < y * y <= f(y);
  }
}

lemma FunctionGrowthRate(x: int)
  requires x > 0
  ensures f(x) >= x * x
{
  DigitSumNonnegative(x);
  assert f(x) == x * x + digitSum(x) * x;
  assert digitSum(x) * x >= 0;
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
  FunctionGrowth(1);
  FunctionGrowthRate(1);
  
  while f(x) < n && x * x <= n
    invariant x >= 1
    invariant forall y :: 1 <= y < x ==> f(y) != n
    invariant f(x) >= x * x
    decreases n - x
  {
    x := x + 1;
    FunctionGrowthRate(x);
  }
  
  if f(x) == n {
    return x;
  } else {
    return -1;
  }
}
// </vc-code>

