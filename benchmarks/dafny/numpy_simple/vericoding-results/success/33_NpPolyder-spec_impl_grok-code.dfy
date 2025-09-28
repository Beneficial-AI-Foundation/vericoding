// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed loop to avoid lower bound exceeding upper bound when result array is empty */
method compute_derivative(coeff: array<real>) returns (res: array<real>)
  requires coeff.Length > 0
  ensures res.Length == coeff.Length - 1
{
  res := new real[coeff.Length - 1];
  if res.Length > 0 {
    for i := 0 to res.Length - 1
    {
      res[i] := coeff[i + 1] * ((i + 1) as real);
    }
  }
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
/* code modified by LLM (iteration 3): Switched to while-loop with invariant to prove length guarantees and helper preconditions */
{
  var current := poly;
  var i := 0;
  while i < m
    invariant 0 <= i <= m && current.Length == poly.Length - i
  {
    current := compute_derivative(current);
    i := i + 1;
  }
  result := current;
}
// </vc-code>
