// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma HelperLemma(n: int, k: int)
  requires 2 <= k < n
  ensures n % k != 0 || n % k == 0
{
}
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
    invariant forall i :: 2 <= i < k ==> n % i != 0
  {
    if n % k == 0 {
      result := true;
      return;
    }
    k := k + 1;
  }
  result := false;
}
// </vc-code>
