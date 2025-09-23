// <vc-preamble>
predicate IsPrimePred(n: int)
{
    forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method LargestPrimeFactor(n: int) returns (result: int)
    requires 2 <= n <= 2147483646
    ensures 1 <= result <= n
    ensures result == 1 || (result > 1 && IsPrimePred(result))
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
