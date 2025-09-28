// <vc-preamble>
/*
 * Legendre polynomial division operations.
 * Implements division of one Legendre series by another, returning quotient and remainder.
 */

// Method to divide one Legendre series by another
// Returns the quotient and remainder of polynomial division in Legendre basis
// </vc-preamble>

// <vc-helpers>
function IsZeroPolynomial(coeffs: seq<real>): bool
{
  forall i :: 0 <= i < |coeffs| ==> coeffs[i] == 0.0
}

function GetLeadingCoeff(coeffs: seq<real>): real
  requires |coeffs| >= 1
  requires exists i :: 0 <= i < |coeffs| && coeffs[i] != 0.0
{
  coeffs[|coeffs| - 1]
}

function MultiplyByScalar(coeffs: seq<real>, scalar: real): seq<real>
{
  seq(|coeffs|, i requires 0 <= i < |coeffs| => coeffs[i] * scalar)
}

function SubtractPolynomials(p1: seq<real>, p2: seq<real>): seq<real>
  requires |p1| >= |p2|
{
  seq(|p1|, i requires 0 <= i < |p1| => if i < |p2| then p1[i] - p2[i] else p1[i])
}

function PadToSize(coeffs: seq<real>, size: int): seq<real>
  requires size >= 1
{
  if |coeffs| >= size then coeffs[..size]
  else coeffs + seq(size - |coeffs|, i => 0.0)
}
// </vc-helpers>

// <vc-spec>
method legdiv(c1: seq<real>, c2: seq<real>) returns (quo: seq<real>, rem: seq<real>)
  requires |c1| >= 1  // dividend has at least one coefficient
  requires |c2| >= 1  // divisor has at least one coefficient  
  requires exists i :: 0 <= i < |c2| && c2[i] != 0.0  // divisor is not zero polynomial
  ensures |quo| == if |c1| >= |c2| then |c1| - |c2| + 1 else 1  // quotient size
  ensures |rem| == if |c2| > 1 then |c2| - 1 else 1  // remainder size
  ensures |c1| < |c2| ==> |quo| == 1 && quo[0] == 0.0  // when dividend degree < divisor degree, quotient is zero
  ensures |rem| <= |c2|  // remainder degree constraint
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed remainder size calculation */
  if |c1| < |c2| {
    quo := [0.0];
    var remainder_size := if |c2| > 1 then |c2| - 1 else 1;
    rem := PadToSize(c1, remainder_size);
  } else {
    var quotient_size := |c1| - |c2| + 1;
    quo := seq(quotient_size, i => 0.0);
    rem := c1;
    
    var step := 0;
    while step < quotient_size && |rem| >= |c2|
      invariant step <= quotient_size
      invariant |quo| == quotient_size
    {
      if |rem| >= |c2| && c2[|c2| - 1] != 0.0 {
        var coeff := rem[|rem| - 1] / c2[|c2| - 1];
        quo := quo[step := coeff];
        
        var term := MultiplyByScalar(c2, coeff);
        if |rem| >= |term| {
          rem := SubtractPolynomials(rem, term);
        }
      }
      step := step + 1;
    }
    
    var remainder_size := if |c2| > 1 then |c2| - 1 else 1;
    rem := PadToSize(rem, remainder_size);
  }
}
// </vc-code>
