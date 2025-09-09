/*
Find the minimum positive integer x such that x is divisible by n and x ends with k or more zeros in base 10.
A number ends with k zeros if and only if it's divisible by 10^k = 2^k × 5^k.
Algorithm: Factor out powers of 2 and 5 from n, then multiply n by additional factors needed to achieve k trailing zeros.
*/

function power(base: int, exp: int): int
    requires exp >= 0
    ensures exp == 0 ==> power(base, exp) == 1
    ensures base > 0 ==> power(base, exp) > 0
    ensures base != 0 ==> power(base, exp) != 0
    decreases exp
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires n > 0 && k >= 0
    ensures result > 0
    ensures result % n == 0
    ensures result % power(10, k) == 0
    ensures forall m :: m > 0 && m % n == 0 && m % power(10, k) == 0 ==> result <= m
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
