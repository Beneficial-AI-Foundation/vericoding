function digitSum(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else (n % 10) + digitSum(n / 10)
}

// <vc-helpers>
lemma square_ge(i: int, x: int)
  requires i >= 0 && x >= i
  ensures x * x >= i * i
{
  // (x - i) * (x + i) = x^2 - i^2, and (x - i) * (x + i) >= 0 when x >= i and i >= 0
  assert (x - i) * (x + i) >= 0;
  assert x * x - i * i == (x - i) * (x + i);
  assert x * x >= i * i;
}

lemma square_gt_from_ge(i: int, x: int, n: int)
  requires i >= 0 && x >= i && i * i > n
  ensures x * x > n
{
  square_ge(i, x);
  assert x * x >= i * i;
  assert i * i > n;
  assert x * x > n;
}

lemma digitSum_nonneg(x: int)
  requires x >= 0
  ensures digitSum(x) >= 0
  decreases x
{
  // By definition of digitSum for non-negative x, it's a sum of digits >= 0.
  if x == 0 {
  } else {
    digitSum_nonneg(x / 10);
  }
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
  var i := 1;
  while i * i <= n
    invariant 1 <= i
    invariant forall y :: 1 <= y < i ==> y * y + digitSum(y) * y != n
    decreases n - i
  {
    if i * i + digitSum(i) * i == n {
      return i;
    } else {
      // record that i does not satisfy the equation before incrementing
      assert i * i + digitSum(i) * i != n;
      i := i + 1;
    }
  }
  // After loop, i*i > n
  assert i * i > n;
  // Prove no x > 0 satisfies the equation
  assert forall x :: x > 0 ==> x * x + digitSum(x) * x != n
  {
    if x < i {
      // x > 0 implies x >= 1, and invariant covers 1 <= x < i
      assert 1 <= x && x < i;
      assert x * x + digitSum(x) * x != n;
    } else {
      // x >= i, so x*x >= i*i > n, and digitSum(x)*x >= 0, hence sum > n
      square_ge(i, x);
      digitSum_nonneg(x);
      assert x * x >= i * i;
      assert i * i > n;
      assert x * x > n;
      assert x * x + digitSum(x) * x > n;
      assert x * x + digitSum(x) * x != n;
    }
  }
  return -1;
}
// </vc-code>

