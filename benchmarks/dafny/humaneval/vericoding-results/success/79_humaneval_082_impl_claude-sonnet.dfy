// <vc-preamble>

predicate is_prime_number(n: int)
{
    n >= 2 && (forall k :: 2 <= k < n ==> n % k != 0)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method prime_length(s: string) returns (result: bool)
    ensures result <==> is_prime_number(|s|)
// </vc-spec>
// <vc-code>
{
  var len := |s|;
  if len < 2 {
    result := false;
  } else {
    result := true;
    var k := 2;
    while k < len
      invariant 2 <= k <= len
      invariant result <==> (forall j :: 2 <= j < k ==> len % j != 0)
    {
      if len % k == 0 {
        result := false;
        break;
      }
      k := k + 1;
    }
  }
}
// </vc-code>
