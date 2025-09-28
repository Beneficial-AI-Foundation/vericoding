// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed from function to method to allow array allocation */
method SingleDerivative(p: array<real>) returns (res: array<real>)
  requires p.Length > 0
  ensures res.Length == p.Length - 1
  ensures forall i :: 0 <= i < res.Length ==> res[i] == (i as real + 1.0) * p[i+1]
{
  res := new real[p.Length - 1];
  for i := 0 to res.Length
    invariant 0 <= i <= res.Length
    invariant res.Length == p.Length - 1
    invariant forall j :: 0 <= j < i ==> res[j] == (j as real + 1.0) * p[j+1]
  {
    res[i] := (i as real + 1.0) * p[i+1];
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
{
    /* code modified by LLM (iteration 2): no change in logic, relies on fixed helper method */
    var current_poly := poly;
    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant current_poly.Length == poly.Length - i
        decreases m - i
    {
        current_poly := SingleDerivative(current_poly);
        i := i + 1;
    }
    result := current_poly;
}
// </vc-code>
