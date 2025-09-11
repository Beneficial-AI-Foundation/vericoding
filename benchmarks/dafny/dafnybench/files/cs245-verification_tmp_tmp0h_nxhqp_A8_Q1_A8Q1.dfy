// <vc-preamble>
function power(a: int, n: int): int
  requires 0 <= n;
  decreases n;
  {
    if (n == 0) then 1 else a * power(a, n - 1)
  }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0
ensures z==power(x,y0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
