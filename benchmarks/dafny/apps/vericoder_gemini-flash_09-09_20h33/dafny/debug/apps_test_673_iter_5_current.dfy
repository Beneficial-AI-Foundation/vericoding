predicate ValidInput(n: int, k: int)
{
    n >= 1 && k > 0
}

predicate IsCorrectResult(n: int, k: int, result: int)
    requires k > 0
{
    result > n && result % k == 0 && forall x :: n < x < result ==> x % k != 0
}

// <vc-helpers>
predicate IsDivisible(a: int, b: int) {
  b != 0 && a % b == 0
}

predicate IsMultipleOfK(x: int, k: int)
  requires k > 0
{
  x % k == 0
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures IsCorrectResult(n, k, result)
// </vc-spec>
// <vc-code>
{
  var result_var := (n / k) * k;
  if result_var <= n {
    result_var := result_var + k;
  }
  
  result := result_var;
  
  // Prove that result > n
  assert result % k == 0; // Trivial from construction
  if n % k == 0 {
    // If n is a multiple of k, then (n/k)*k == n
    // So result_var would be n initially.
    // Since result_var <= n is true, result_var becomes n+k.
    // Thus result = n+k, and n+k > n.
  } else {
    // If n is not a multiple of k, then (n/k)*k < n.
    // So result_var starts as a multiple of k less than n.
    // It keeps adding k until it's > n.
    // For example, if n=5, k=3:
    // result_var = (5/3)*3 = 1*3 = 3.
    // 3 <= 5, so result_var = 3+3=6. So result=6. 6>5.
    // What if n=7, k=3:
    // result_var = (7/3)*3 = 2*3 = 6.
    // 6 <= 7, so result_var = 6+3=9. So result=9. 9>7.
    // In all cases, result_var (the initial value) is result_var' = (n/k)*k.
    // We know result_var' <= n as long as n is not a multiple of k (if n is a multiple, result_var' = n).
    // if result_var' <= n: result_var = result_var' + k.
    // We need to show result_var' + k > n.
    // Since result_var' % k == 0 (by construction), and result_var' <= n,
    // the next multiple of k which is >= n must be either n (if n%k==0) or result_var'+k.
    // We want the smallest multiple of k which is greater than n.
    // Let m = result_var' = (n/k)*k.
    // If m <= n, then result = m + k.
    // We need to prove m + k > n.
    // We know m <= n.
    // We also know n < m + k. This is because m is the largest multiple of k which is less than or equal to n.
    // Therefore, any multiple of k greater than m must be m + k, m + 2k, etc.
    // Since n is between m and m+k (if n is not equal to m), then m < n < m+k.
    // If n == m, then n is a multiple of k, and result would be n+k, which is > n.
    // So in all cases, result > n.
  }

  // Prove IsCorrectResult.forall x :: n < x < result ==> x % k != 0
  // Let result = m. We know m % k == 0.
  // We need to show that there is no x such that n < x < m and x % k == 0.
  // We found m by finding the first multiple of k that is strictly greater than n.
  // If n is a multiple of k, then (n/k)*k = n. So result = n + k.
  // Then we need to show that no x, n < x < n+k, has x % k == 0. This is true by definition of k. The only multiple of k between n (inclusive) and n+k (exclusive) is n itself.
  // If n is not a multiple of k, then (n/k)*k < n. Let this be m'.
  // Our result is m' + k.
  // We know m' < n < m' + k.
  // We need to show that there's no x such that n < x < m' + k and x % k == 0.
  // The only multiple of k greater than or equal to m' and less than or equal to m' + k is m' + k itself.
  // Since n < m' + k, if there were another multiple of k between n and m'+k, it would have to be m' itself or some multiple of k between m' and m'+k.
  // But m' < n, so m' is not in (n, m'+k).
  // So the only multiple of k in (n, m'+k) that we could find is m'+k (exclusive upper bound).
  // Thus, the closest multiple of k greater than n is result. No other multiples of k exist strictly between n and result.
}
// </vc-code>

