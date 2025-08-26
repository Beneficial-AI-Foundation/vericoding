// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (exists k :: 2 <= k < n && n % k == 0)
// </vc-spec>
// <vc-code>
{
  var k := 2;
  result := false;
  
  while k < n
    invariant 2 <= k <= n
    invariant result <==> (exists j :: 2 <= j < k && n % j == 0)
  {
    if n % k == 0 {
      result := true;
      return;
    }
    k := k + 1;
  }
  
  // At this point k == n, and we need to establish the postcondition
  // result is false, so we need to show that !(exists k :: 2 <= k < n && n % k == 0)
  // which means (forall k :: 2 <= k < n ==> n % k != 0)
  // This follows from the loop invariant: result <==> (exists j :: 2 <= j < k && n % j == 0)
  // Since result is false and k == n, we have !(exists j :: 2 <= j < n && n % j == 0)
}
// </vc-code>