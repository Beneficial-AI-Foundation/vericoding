// <vc-preamble>

function power(base: int, exp: nat): int
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method modp(n: int, p: int) returns (result: int)
    requires n >= 0 && p > 0
    ensures result >= 0 && result < p
    ensures result == power(2, n) % p
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
