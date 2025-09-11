// <vc-preamble>
function verifyNeg(a: array<int>, idx: int) : nat
reads a
requires 0 <= idx <= a.Length
{
    if idx == 0 then 0 
    else verifyNeg(a, idx - 1) + (if a[idx - 1] < 0 then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountNeg(a: array<int>) returns (cnt: nat) 
ensures cnt == verifyNeg(a, a.Length)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
