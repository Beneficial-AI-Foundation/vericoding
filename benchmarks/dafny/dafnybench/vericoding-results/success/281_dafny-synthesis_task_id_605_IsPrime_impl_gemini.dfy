// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (forall k :: 2 <= k < n ==> n % k != 0)
// </vc-spec>
// <vc-code>
{
  var k := 2;
  while k < n
    invariant 2 <= k <= n
    invariant forall j :: 2 <= j < k ==> n % j != 0
  {
    if n % k == 0 {
      result := false;
      return;
    }
    k := k + 1;
  }
  result := true;
}
// </vc-code>
