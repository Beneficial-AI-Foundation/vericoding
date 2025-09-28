// <vc-preamble>

predicate is_prime_number(n: int)
{
    n >= 2 && forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_prime(n: int) returns (result: bool)
    ensures result <==> is_prime_number(n)
// </vc-spec>
// <vc-code>
{
  if n < 2 {
    result := false;
  } else {
    result := true;
    var k := 2;
    while k < n
      invariant 2 <= k <= n
      invariant result <==> (forall j :: 2 <= j < k ==> n % j != 0)
    {
      if n % k == 0 {
        result := false;
        break;
      }
      k := k + 1;
    }
  }
}
// </vc-code>
