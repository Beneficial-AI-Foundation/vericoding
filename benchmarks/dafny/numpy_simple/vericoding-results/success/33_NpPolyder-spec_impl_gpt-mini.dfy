// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): use 'function' and 'as real' cast to fix syntax */
function falling_factor(n: int, m: int): real
  requires n >= m && m >= 0
{
  if m == 0 then 1.0 else (n as real) * falling_factor(n - 1, m - 1)
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
  /* code modified by LLM (iteration 2): compute m-th derivative coefficients using falling factorial product */
  result := new real[poly.Length - m];
  var L := poly.Length;
  var Rlen := L - m;
  var i := 0;
  while i < Rlen
    invariant 0 <= i <= Rlen
    invariant Rlen == poly.Length - m
    invariant result.Length == Rlen
  {
    var idx := i + m;
    var mult := 1.0;
    var k := 0;
    while k < m
      invariant 0 <= k <= m
    {
      mult := mult * ((idx - k) as real);
      k := k + 1;
    }
    result[i] := poly[idx] * mult;
    i := i + 1;
  }
}
// </vc-code>
