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
    var i := 2;
    result := true;
    while i < len
      invariant 2 <= i <= len
      invariant result <==> (forall k :: 2 <= k < i ==> len % k != 0)
    {
      if len % i == 0 {
        result := false;
        break;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
