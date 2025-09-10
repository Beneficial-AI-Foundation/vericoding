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
  // At this point i*i > n
  assert i * i > n;

  // Prove for all x > 0 that x*x + digitSum(x)*x != n
  assert forall x :: x > 0 ==> x * x + digitSum(x) * x != n
  {
    var x0 := arbitrary int;
    assume x0 > 0;
    if x0 < i {
      // Covered by loop invariant
      assert 1 <= x0 < i;
      assert x0 * x0 + digitSum(x0) * x0 != n;
    } else {
      // For x0 >= i we have x0*x0 > n, and digitSum(x0) >= 0, so sum > n
      digitSum_nonneg(x0);
      square_gt_from_ge(i, x0, n);
      assert x0 * x0 > n;
      assert x0 * x0 + digitSum(x0) * x0 > n;
    }
  }

  return -1;
}
// </vc-code>

