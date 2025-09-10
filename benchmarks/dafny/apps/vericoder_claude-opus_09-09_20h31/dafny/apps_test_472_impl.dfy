function digitSum(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else (n % 10) + digitSum(n / 10)
}

// <vc-helpers>
lemma digitSumPositive(x: int)
  requires x > 0
  ensures digitSum(x) >= 1
  decreases x
{
  if x < 10 {
    assert x >= 1;
    assert digitSum(x) == x % 10 == x >= 1;
  } else {
    assert x % 10 >= 0;
    digitSumPositive(x / 10);
    assert digitSum(x / 10) >= 1;
    assert digitSum(x) == (x % 10) + digitSum(x / 10) >= 1;
  }
}

lemma boundHelper(x: int, n: int)
  requires x > 0
  requires n >= 1
  requires x * x > n
  ensures x * x + digitSum(x) * x > n
{
  digitSumPositive(x);
  assert digitSum(x) >= 1;
  assert digitSum(x) * x >= x;
  assert x * x + digitSum(x) * x >= x * x + x > n;
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
  while x * x <= n
    invariant x >= 1
    invariant forall y :: 0 < y < x ==> y * y + digitSum(y) * y != n
    decreases n - x * x + 1
  {
    if x * x + digitSum(x) * x == n {
      return x;
    }
    x := x + 1;
  }
  
  // At this point, x * x > n
  // We need to prove that no y >= x can satisfy the equation
  assert x * x > n;
  
  // For any y >= x, we have y * y >= x * x > n
  // So y * y + digitSum(y) * y >= y * y > n
  forall y | y >= x
    ensures y * y + digitSum(y) * y != n
  {
    if y > 0 {
      assert y * y >= x * x > n;
      boundHelper(y, n);
      assert y * y + digitSum(y) * y > n;
    }
  }
  
  // Combine with the loop invariant to get the full postcondition
  assert forall y :: 0 < y < x ==> y * y + digitSum(y) * y != n;
  assert forall y :: y >= x && y > 0 ==> y * y + digitSum(y) * y != n;
  assert forall y :: y > 0 ==> y * y + digitSum(y) * y != n;
  
  return -1;
}
// </vc-code>

