

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
  var i := n - 1;
  while i > 1 && n % i != 0
    invariant 1 <= i < n
    invariant forall k :: i < k < n ==> n % k != 0
    decreases i
  {
    i := i - 1;
  }
  d := i;
}
// </vc-code>

