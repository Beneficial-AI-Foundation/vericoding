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
    var i := 2;
    while (i < n)
      invariant i >= 2 && i <= n
      invariant forall k :: 2 <= k < i ==> n % k != 0
      decreases n - i
    {
      if n % i == 0 {
        result := false;
        break;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
