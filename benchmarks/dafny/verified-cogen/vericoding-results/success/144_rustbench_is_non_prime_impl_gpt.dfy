// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate HasNonTrivialDivisor(n: int) { exists k :: 2 <= k < n && n % k == 0 }
// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result == exists k :: 2 <= k < n && n % k == 0
// </vc-spec>
// <vc-code>
{
  var k := 2;
  result := false;
  while k < n
    invariant 2 <= k <= n
    invariant result ==> exists d :: 2 <= d < k && n % d == 0
    invariant !result ==> (forall d :: 2 <= d < k ==> n % d != 0)
    decreases n - k
  {
    if n % k == 0 {
      result := true;
    }
    k := k + 1;
  }
}
// </vc-code>
