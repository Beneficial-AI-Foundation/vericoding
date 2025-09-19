// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ChebDer(c: seq<real>, scl: real := 1.0) returns (result: seq<real>)
  // Input must have at least one coefficient
  requires |c| >= 1
  // Output has one fewer coefficient than input
  ensures |result| == |c| - 1
  // Base case: when result has at least 1 element, result[0] = scl * c[1] 
  ensures |result| >= 1 ==> result[0] == scl * c[1]
  // Base case: when result has at least 2 elements, result[1] = scl * 4 * c[2]
  ensures |result| >= 2 ==> result[1] == scl * 4.0 * c[2]
  // General recurrence: for j >= 2, result[j] = scl * (2 * (j+1)) * c[j+1]
  ensures forall j :: 2 <= j < |result| ==> 
    result[j] == scl * (2.0 * (j + 1) as real) * c[j + 1]
  // All coefficients in result are well-defined based on input coefficients
  ensures forall j :: 0 <= j < |result| ==> j + 1 < |c|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
