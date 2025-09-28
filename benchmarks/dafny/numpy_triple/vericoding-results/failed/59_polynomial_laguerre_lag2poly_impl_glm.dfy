// <vc-preamble>
// Helper function to evaluate a Laguerre polynomial at a given point
function EvaluateLaguerrePolynomial(coeffs: seq<real>, x: real): real
  requires |coeffs| > 0
{
  if |coeffs| == 1 then
    coeffs[0]
  else
    coeffs[0] + EvaluateLaguerrePolynomial(coeffs[1..], x) * LaguerrePolynomialValue(|coeffs| - 1, x)
}

// Helper function to compute the value of the nth Laguerre polynomial at x
function LaguerrePolynomialValue(n: nat, x: real): real
{
  if n == 0 then 1.0
  else if n == 1 then 1.0 - x
  else 
    ((2.0 * n as real - 1.0 - x) * LaguerrePolynomialValue(n - 1, x) - (n as real - 1.0) * LaguerrePolynomialValue(n - 2, x)) / n as real
}

// Helper function to evaluate a standard polynomial at a given point  
function EvaluatePolynomial(coeffs: seq<real>, x: real): real
  requires |coeffs| > 0
{
  if |coeffs| == 1 then
    coeffs[0]
  else
    coeffs[0] + x * EvaluatePolynomial(coeffs[1..], x)
}

// Convert a Laguerre series to a polynomial
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed sequence bounds and added proper indexing */
function CreateZeroSequence(length: nat): seq<real>
{
  if length == 0 then [] else [0.0] + CreateZeroSequence(length - 1)
}

function SequenceAdd(s1: seq<real>, s2: seq<real>): seq<real>
  requires |s1| == |s2|
{
  if |s1| == 0 then [] else [s1[0] + s2[0]] + SequenceAdd(s1[1..], s2[1..])
}

function SequenceSubtract(s1: seq<real>, s2: seq<real>): seq<real>
  requires |s1| == |s2|
{
  if |s1| == 0 then [] else [s1[0] - s2[0]] + SequenceSubtract(s1[1..], s2[1..])
}

function SequenceMultiplyScalar(s: seq<real>, scalar: real): seq<real>
{
  if |s| == 0 then [] else [s[0] * scalar] + SequenceMultiplyScalar(s[1..], scalar)
}

function SequenceShiftRight(s: seq<real>): seq<real>
{
  [0.0] + s
}
// </vc-helpers>

// <vc-spec>
method Lag2Poly(c: seq<real>) returns (result: seq<real>)
  requires |c| > 0
  ensures |result| == |c|
  ensures forall x: real :: EvaluatePolynomial(result, x) == EvaluateLaguerrePolynomial(c, x)
  ensures |c| == 1 ==> result == c
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed loop bounds and indexing */
{
  var n := |c| - 1;
  if n == 0 {
    return c;
  }

  var M: seq<seq<real>> := [];
  M := M + [[1.0] + CreateZeroSequence(n)];
  if n >= 1 {
    M := M + [[1.0, -1.0] + CreateZeroSequence(n-1)];
  }

  for i := 2 to n {
    var term1 := SequenceMultiplyScalar(M[i-1], (2.0 * i as real - 1.0));
    
    var term2 := SequenceShiftRight(M[i-1]);
    
    var temp := SequenceSubtract(term1, term2);
    
    temp := SequenceSubtract(temp, SequenceMultiplyScalar(M[i-2], (i-1) as real));
    
    temp := SequenceMultiplyScalar(temp, 1.0 / (i as real));
    
    M := M + [temp];
  }

  var polyResult := CreateZeroSequence(n+1);
  for i := 0 to n {
    if i < |c| {
      var term := SequenceMultiplyScalar(M[i], c[i]);
      polyResult := SequenceAdd(polyResult, term);
    }
  }

  return polyResult;
}
// </vc-code>
