// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result == exists k :: 2 <= k < n && n % k == 0
// </vc-spec>
// <vc-code>
{
  var k := 2;
  while k < n
    invariant 2 <= k <= n
    invariant forall j :: 2 <= j < k ==> n % j != 0
  {
    if n % k == 0 {
      return true;
    }
    k := k + 1;
  }
  return false;
}
// </vc-code>
