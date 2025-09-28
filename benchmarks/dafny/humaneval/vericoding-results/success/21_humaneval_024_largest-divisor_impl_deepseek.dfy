// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

lemma helper_divisor_property(n: int, k: int)
  requires n > 1 && 1 <= k < n
  ensures n % k != 0 || k <= n / 2
{
  if k > n / 2 {
    assert n % k == n - k * (n / k);
    assert n % k != 0 || n % k == n - k;
    assert n - k < k;
  }
}

// </vc-helpers>

// <vc-spec>
method largest_divisor(n: int) returns (d : int)

  requires n > 1

  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Iterate backwards starting from n-1 down to 1 */
  d := 1;
  var i := n - 1;
  
  while i >= 1
    invariant 1 <= i <= n - 1 || i == 0
    invariant forall k :: i < k < n ==> n % k != 0
    invariant d == 1 || (d >= i && n % d == 0)
    decreases i
  {
    if n % i == 0 {
      d := i;
      break;
    }
    i := i - 1;
  }
  
  assert forall k :: d < k < n ==> n % k != 0;
}
// </vc-code>
