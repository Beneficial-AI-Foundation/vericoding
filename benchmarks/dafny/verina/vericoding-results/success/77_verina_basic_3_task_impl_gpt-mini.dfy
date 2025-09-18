// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma DivBy11Inverse(n: int, k: int)
  requires k * 11 == n
  ensures n / 11 == k
{
  // n equals k*11 by assumption
  assert n == k * 11;
  // therefore the remainder of n modulo 11 is 0
  assert n % 11 == (k * 11) % 11;
  assert (k * 11) % 11 == 0;
  // division identity: n == (n / 11) * 11 + n % 11
  assert n == (n / 11) * 11 + n % 11;
  // substitute remainder 0
  assert n == (n / 11) * 11;
  // now k*11 == (n / 11) * 11, canceling 11 (which is nonzero) yields k == n/11
  assert k * 11 == (n / 11) * 11;
  assert k == n / 11;
}
// </vc-helpers>

// <vc-spec>
method IsDivisibleBy11(n: int) returns (result: bool)
    ensures result <==> (exists k: int :: k * 11 == n)
// </vc-spec>
// <vc-code>
{
  var q := n / 11;
  result := (q * 11 == n);
}

// </vc-code>
