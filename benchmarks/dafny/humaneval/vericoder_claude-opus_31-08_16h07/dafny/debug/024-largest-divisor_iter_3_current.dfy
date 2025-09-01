

// <vc-helpers>
lemma LargestDivisorCorrect(n: int, i: int, d: int)
  requires n > 1
  requires 2 <= i < n
  requires n % i == 0
  requires d == n / i
  requires forall k :: 2 <= k < i ==> n % k != 0
  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
{
  // d = n/i and i >= 2, so d <= n/2 < n
  assert d * i == n;
  assert d >= 1;
  assert d < n;
  assert n % d == 0;
  
  // For any k where d < k < n, if n % k == 0, then n/k would be a divisor < i
  // We prove by contradiction
  if exists k :: d < k < n && n % k == 0 {
    var k :| d < k < n && n % k == 0;
    var j := n / k;
    assert j * k == n;
    // Since k > d = n/i, we have j = n/k < n/(n/i) = i
    assert j < i;
    // Since k < n, we have j = n/k > n/n = 1, so j >= 2
    assert j >= 2;
    assert n % j == 0;
    // This contradicts the precondition that no divisor exists in [2, i)
    assert false;
  }
}
// </vc-helpers>

// <vc-spec>
method largest_divisor(n: int) returns (d : int)
  // pre-conditions-start
  requires n > 1
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant forall k :: 2 <= k < i ==> n % k != 0
  {
    if n % i == 0 {
      d := n / i;
      LargestDivisorCorrect(n, i, d);
      return;
    }
    i := i + 1;
  }
  d := 1;
}
// </vc-code>

