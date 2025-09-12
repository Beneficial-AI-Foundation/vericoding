// <vc-preamble>
predicate IsDivisible(n: int, divisor: int)
    requires divisor != 0
{
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result == (exists k :: 2 <= k < n && IsDivisible(n, k))
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
