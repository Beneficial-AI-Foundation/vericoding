// <vc-preamble>

predicate is_prime_number(n: int)
{
    n >= 2 && (forall k :: 2 <= k < n ==> n % k != 0)
}
// </vc-preamble>

// <vc-helpers>
lemma DivisorImpliesComposite(n: int, d: int)
  requires 2 <= d < n
  requires n % d == 0
  ensures !is_prime_number(n)
{
  assert exists k :: 2 <= k < n && n % k == 0;
}

lemma NoDivisorsImpliesPrime(n: int)
  requires n >= 2
  requires forall k :: 2 <= k < n ==> n % k != 0
  ensures is_prime_number(n)
{
  assert n >= 2;
  assert forall k :: 2 <= k < n ==> n % k != 0;
  assert is_prime_number(n);
}

// </vc-helpers>

// <vc-spec>
method prime_length(s: string) returns (result: bool)
    ensures result <==> is_prime_number(|s|)
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  if n < 2 {
    result := false;
    return;
  }
  var k := 2;
  var ok := true;
  while k < n
    invariant 2 <= k <= n
    invariant ok <==> (forall j :: 2 <= j < k ==> n % j != 0)
    decreases n - k
  {
    if n % k == 0 {
      ok := false;
      k := n;
    } else {
      k := k + 1;
    }
  }
  result := ok;
}

// </vc-code>
