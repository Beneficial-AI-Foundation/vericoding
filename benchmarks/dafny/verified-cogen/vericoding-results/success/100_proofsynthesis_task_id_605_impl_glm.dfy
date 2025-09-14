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
method PrimeNum(n: int) returns (result: bool)
    requires n >= 2
    ensures result == (forall k :: 2 <= k < n ==> !IsDivisible(n, k))
// </vc-spec>
// <vc-code>
{
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant forall k :: 2 <= k < i ==> !IsDivisible(n, k)
  {
    if IsDivisible(n, i) {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>
