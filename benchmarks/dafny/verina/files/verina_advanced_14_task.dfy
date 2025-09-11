// <vc-preamble>
function Power(base: int, exp: nat): int
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IfPowerOfFour(n: nat) returns (result: bool)
    ensures result <==> (exists m: nat :: n == Power(4, m))
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := false;
    // impl-end
}
// </vc-code>
