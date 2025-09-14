

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (forall k :: 2 <= k < n ==> n % k != 0)
// </vc-spec>
// <vc-code>
{
  result := true;
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant result <==> (forall k :: 2 <= k < i ==> n % k != 0)
  {
    if n % i == 0 {
      result := false;
      break;
    }
    i := i + 1;
  }
}
// </vc-code>

