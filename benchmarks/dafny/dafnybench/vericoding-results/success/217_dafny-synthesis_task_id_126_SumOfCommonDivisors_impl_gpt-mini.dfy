

// <vc-helpers>
// No helper functions needed for this proof.
// </vc-helpers>

// <vc-spec>
method SumOfCommonDivisors(a: int, b: int) returns (sum: int)
    requires a > 0 && b > 0
    ensures sum >= 0
    ensures forall d :: 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d
// </vc-spec>
// <vc-code>
{
  var m := if a < b then a else b;
  sum := 0;
  var i := 1;
  while i <= m
    invariant 1 <= i <= m + 1
    invariant sum >= 0
    invariant sum <= i - 1
    invariant forall d :: 1 <= d <= i - 1 && d <= a && d <= b && a % d == 0 && b % d == 0 ==> sum >= d
  {
    if a % i == 0 && b % i == 0 {
      sum := i;
    }
    i := i + 1;
  }
}
// </vc-code>

