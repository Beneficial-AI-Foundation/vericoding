// <vc-preamble>
// Method that creates a coefficient vector for the linear polynomial off + scl*x
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method polyline(off: real, scl: real) returns (result: seq<real>)
  // The result is always a 2-element sequence representing polynomial coefficients
  ensures |result| == 2
  
  // Constant term is always off (coefficient of x^0)
  ensures result[0] == off
  
  // Linear coefficient is always scl (coefficient of x^1)
  ensures result[1] == scl
  
  // Mathematical property: polynomial evaluation at x=0 gives the constant term
  ensures result[0] + result[1] * 0.0 == off
  
  // Mathematical property: polynomial evaluation at x=1 gives off + scl
  ensures result[0] + result[1] * 1.0 == off + scl
  
  // The coefficients correctly represent the linear polynomial off + scl*x
  ensures forall x: real {:trigger result[1] * x} :: result[0] + result[1] * x == off + scl * x
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
