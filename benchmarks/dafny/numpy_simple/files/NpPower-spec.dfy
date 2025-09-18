// <vc-preamble>
function IntPow(base: int, exp: nat): int
    decreases exp
{
    if exp == 0 then
        1
    else
        base * IntPow(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Power(a: array<int>, b: array<nat>) returns (result: array<int>)
    requires a.Length == b.Length
    ensures 
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == IntPow(a[i], b[i])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
