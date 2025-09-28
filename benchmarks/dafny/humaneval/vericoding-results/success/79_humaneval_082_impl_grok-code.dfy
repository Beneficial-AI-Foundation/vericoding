// <vc-preamble>

predicate is_prime_number(n: int)
{
    n >= 2 && (forall k :: 2 <= k < n ==> n % k != 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added invariant to prove primality */
method is_prime(n: int) returns (result: bool)
  requires n >= 0
  ensures result <==> is_prime_number(n)
{
  if n < 2 {
    result := false;
  } else {
    result := true;
    var k := 2;
    while k < n
      decreases n - k
      invariant k >= 2
      invariant result == (forall i :: 2 <= i < k ==> n % i != 0)
    {
      if n % k == 0 {
        result := false;
        return;
      }
      k := k + 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method prime_length(s: string) returns (result: bool)
    ensures result <==> is_prime_number(|s|)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): fixed method call syntax and assigned to result */
  result := is_prime(|s|);
}
// </vc-code>
