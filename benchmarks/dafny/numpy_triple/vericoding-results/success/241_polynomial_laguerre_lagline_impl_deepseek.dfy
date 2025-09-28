// <vc-preamble>
// Creates a Laguerre series representation of the straight line off + scl*x
// </vc-preamble>

// <vc-helpers>

function lagline_coeff0(off: real, scl: real): (a0: real)
  ensures a0 == off + scl
{
  off + scl
}

function lagline_coeff1(off: real, scl: real): (a1: real)
  ensures a1 == -scl
{
  -scl
}

// </vc-helpers>

// <vc-spec>
method lagline(off: real, scl: real) returns (result: seq<real>)
  // The result is always a sequence of exactly 2 coefficients
  ensures |result| == 2
  // When scl is zero, we have a constant function off, represented as [off, 0]
  ensures scl == 0.0 ==> result[0] == off && result[1] == 0.0
  // When scl is non-zero, the Laguerre representation requires specific coefficients
  ensures scl != 0.0 ==> result[0] == off + scl && result[1] == -scl
// </vc-spec>
// <vc-code>
{
  var coeff0 := lagline_coeff0(off, scl);
  var coeff1 := lagline_coeff1(off, scl);
  result := [coeff0, coeff1];
}
// </vc-code>
