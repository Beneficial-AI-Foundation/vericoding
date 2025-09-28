// <vc-preamble>
predicate IsDivisible(n: int, divisor: int)
    requires divisor != 0
{
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result == (exists k :: 2 <= k < n && IsDivisible(n, k))
// </vc-spec>
// <vc-code>
{
  var k := 2;
  while k < n
    invariant 2 <= k <= n
    invariant forall i :: 2 <= i < k ==> !IsDivisible(n, i)
  {
    if IsDivisible(n, k) {
      result := true;
      return;
    }
    k := k + 1;
  }
  result := false;
}
// </vc-code>
