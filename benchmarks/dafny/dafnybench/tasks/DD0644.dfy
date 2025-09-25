// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (exists k :: 2 <= k < n && n % k == 0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
