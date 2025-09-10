

// <vc-helpers>
// no helpers needed
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
  var i := 1;
  d := 1;
  while i < n
    invariant 1 <= d < n
    invariant n % d == 0
    invariant 1 <= i <= n
    invariant forall k :: d < k < i ==> n % k != 0
    decreases n - i
  {
    if n % i == 0 && i > d {
      d := i;
    }
    i := i + 1;
  }
}
// </vc-code>

