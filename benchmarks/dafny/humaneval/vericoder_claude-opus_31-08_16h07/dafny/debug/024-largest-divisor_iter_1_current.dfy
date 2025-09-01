

// <vc-helpers>
// No additional helpers needed
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
      assert 1 <= d < n;
      assert n % d == 0;
      assert forall k :: d < k < n ==> n % k != 0;
      return;
    }
    i := i + 1;
  }
  d := 1;
}
// </vc-code>

