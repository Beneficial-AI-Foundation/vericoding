// <vc-preamble>
function Power(n:nat):nat 
{
    if n == 0 then 1 else 2 * Power(n-1)
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method CalcPower(n:nat) returns (p:nat)
    ensures p == 2*n;
// </vc-spec>
// <vc-code>
{
    p := 2*n;
}
// </vc-code>
