

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
  var found := false;
  while k < n
    invariant 2 <= k <= n
    invariant found <==> (exists j :: 2 <= j < k && n % j == 0)
    decreases n - k
  {
    if n % k == 0 {
      found := true;
    }
    k := k + 1;
  }
  result := found;
}
// </vc-code>

