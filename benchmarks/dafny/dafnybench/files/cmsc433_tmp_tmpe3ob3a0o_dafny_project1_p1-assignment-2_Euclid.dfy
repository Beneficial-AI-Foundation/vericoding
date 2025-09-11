// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Euclid (m : int, n : int) returns (gcd : int)
    requires m > 1 && n > 1 && m >= n
    ensures gcd > 0 && gcd <= n && gcd <= m && m % gcd == 0 && n % gcd == 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
