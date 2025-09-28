// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 2): fixed invalid ParensExpression by removing real() cast */
  result := new real[poly.Length - m];
  var i := 0;
  while i < result.Length
    invariant 0 <= i <= result.Length
  {
    var coeff := poly[i + m];
    var j := 0;
    while j < m
      invariant 0 <= j <= m
    {
      coeff := coeff * (i + m - j) as real;
      j := j + 1;
    }
    result[i] := coeff;
    i := i + 1;
  }
}
// </vc-code>
