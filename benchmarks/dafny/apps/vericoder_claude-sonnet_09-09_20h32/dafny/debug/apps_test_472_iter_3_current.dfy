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
  ensures digitSum(x) <= 9 * (x - 1) / 1 + 9
{
  if x < 10 {
    assert digitSum(x) == x <= 9;
  } else {
    DigitSumBound(x / 10);
    assert digitSum(x) == (x % 10) + digitSum(x / 10);
    assert x % 10 <= 9;
    assert x / 10 >= 1;
    assert digitSum(x / 10) <= 9 * ((x / 10) - 1) / 1 + 9;
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
  assert f(x) == x * x + digitSum(x) * x;
  assert f(y) == y * y + digitSum(y) * y;
  assert x * x + digitSum(x) * x < y * y + digitSum(y) * y;
}

lemma FunctionBound(x: int)
  requires x > 0
  ensures f(x) <= x * x + 9 * (x - 1) * x / 1 + x
{
  DigitSumNonnegative(x);
  DigitSumBound(x);
  assert digitSum(x) <= 9 * (x - 1) / 1 + 9;
  if x == 1 {
    assert digitSum(1) == 1;
    assert f(1) == 1 * 1 + 1 * 1 == 2;
    assert 1 * 1 + 9 * (1 - 1) * 1 / 1 + 1 == 1 + 0 + 1 == 2;
  } else {
    assert digitSum(x) * x <= (9 * (x - 1) / 1 + 9) * x;
    assert (9 * (x - 1) / 1 + 9) * x == 9 * (x - 1) * x / 1 + 9 * x;
    assert f(x) == x * x + digitSum(x) * x <= x * x + 9 * (x - 1) * x / 1 + 9 * x;
    assert 9 * x >= x;
    assert f(x) <= x * x + 9 * (x - 1) * x / 1 + x;
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
  
  while f(x) < n
    invariant x >= 1
    invariant forall y :: 1 <= y < x ==> f(y) != n
    invariant f(x) < n ==> f(x) >= x * x
    decreases n - f(x)
  {
    x := x + 1;
    FunctionGrowthRate(x);
  }
  
  if f(x) == n {
    return x;
  } else {
    assert f(x) > n;
    assert forall y :: 1 <= y < x ==> f(y) != n;
    assert forall y :: y >= x ==> f(y) >= f(x) > n by {
      forall y | y >= x && y > 0
        ensures f(y) >= f(x)
      {
        if y > x {
          FunctionMonotonic(x, y);
        }
      }
    }
    assert forall y :: y > 0 ==> f(y) != n;
    return -1;
  }
}
// </vc-code>

