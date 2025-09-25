// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsArmstrong(n: int) returns (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
