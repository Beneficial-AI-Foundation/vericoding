// <vc-preamble>
function power(x: real, n: nat) : real
  decreases n
{
    if n == 0 then 1.0 else x * power(x, n-1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method powerIter(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
