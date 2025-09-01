

// <vc-helpers>

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
  var k := n - 1;
  while k >= 1
    invariant 1 <= k <= n - 1
    invariant forall x :: k < x < n ==> n % x != 0
  {
    if n % k == 0 {
      return k;
    }
    k := k - 1;
  }
  return 1; // Should not be reached given precondition n > 1
}
// </vc-code>

