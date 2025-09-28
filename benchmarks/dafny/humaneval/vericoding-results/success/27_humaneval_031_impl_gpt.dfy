// <vc-preamble>

predicate is_prime_number(n: int)
{
    n >= 2 && forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
lemma DivisorImpliesNotPrime(n: int, k: int)
  requires 2 <= k < n
  requires n % k == 0
  ensures !is_prime_number(n)
{
  assert n >= 2;
  assert exists t :: 2 <= t < n && n % t == 0;
}
// </vc-helpers>

// <vc-spec>
method is_prime(n: int) returns (result: bool)
    ensures result <==> is_prime_number(n)
// </vc-spec>
// <vc-code>
{
  if n < 2 {
    result := false;
    return;
  }
  var k := 2;
  while k < n
    invariant 2 <= k <= n
    invariant forall j :: 2 <= j < k ==> n % j != 0
    decreases n - k
  {
    if n % k == 0 {
      result := false;
      DivisorImpliesNotPrime(n, k);
      return;
    }
    k := k + 1;
  }
  assert k == n;
  result := true;
}
// </vc-code>
