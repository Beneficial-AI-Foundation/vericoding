// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsDivisor(n: int, d: int)
{
  d != 0 && n % d == 0
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
  var i := 2;
  var best := 1;
  while i < n
    invariant 2 <= i <= n
    invariant 1 <= best < n
    invariant best < i
    invariant n % best == 0
    invariant forall t :: best < t < i ==> n % t != 0
  {
    if n % i == 0 {
      best := i;
    }
    i := i + 1;
  }
  d := best;
}
// </vc-code>
