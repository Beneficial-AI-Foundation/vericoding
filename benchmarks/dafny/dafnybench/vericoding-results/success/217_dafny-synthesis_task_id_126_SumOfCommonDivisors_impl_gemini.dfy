// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(x: int, y: int): int { if x <= y then x else y }
// </vc-helpers>

// <vc-spec>
method SumOfCommonDivisors(a: int, b: int) returns (sum: int)
    requires a > 0 && b > 0
    ensures sum >= 0
    ensures forall d :: 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d
// </vc-spec>
// <vc-code>
{
  sum := 0;
  var i := 1;
  var limit := min(a, b);
  while i <= limit
    invariant 1 <= i <= limit + 1
    invariant sum >= 0
    invariant forall d :: 1 <= d < i && a % d == 0 && b % d == 0 ==> sum >= d
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
    }
    i := i + 1;
  }
}
// </vc-code>
