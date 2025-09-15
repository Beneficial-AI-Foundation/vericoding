// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsDivisor(n: int, d: int): bool { d >= 1 && d < n && n % d == 0 }
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
  d := n / 2;
  while d >= 1
    invariant 1 <= d <= n / 2
    invariant forall k :: d < k < n ==> n % k != 0
  {
    if n % d == 0 {
      return d;
    }
    d := d - 1;
  }
  return 1;
}
// </vc-code>
