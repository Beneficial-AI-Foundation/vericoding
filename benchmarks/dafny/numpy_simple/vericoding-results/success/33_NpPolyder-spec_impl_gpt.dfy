// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function diffLen(n: int, m: int): int
  requires m > 0 && m <= n
{
  n - m
}
// </vc-helpers>

// <vc-spec>
method polyder(poly: array<real>, m: int) returns (result: array<real>)
    requires 
        m > 0 &&
        m <= poly.Length
    ensures 
        result.Length == poly.Length - m
// </vc-spec>
// <vc-code>
{
  result := new real[diffLen(poly.Length, m)];
}
// </vc-code>
