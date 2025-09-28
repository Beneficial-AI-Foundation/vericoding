// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var i := n - 1;
  while i >= 1
    invariant 1 <= i < n
    invariant forall k :: i < k < n ==> n % k != 0
    decreases i
  {
    if n % i == 0 {
      d := i;
      return;
    }
    i := i - 1;
  }
}
// </vc-code>
