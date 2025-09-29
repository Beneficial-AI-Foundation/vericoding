// <vc-preamble>
// Mathematical helper functions for specification
function Exp(x: real): real
  requires true
{
  1.0 // Placeholder for exponential function
}

function Abs(x: real): real
{
  if x >= 0.0 then x else -x
}

// Hyperbolic cosine element-wise computation
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method numpy_cosh(x: seq<real>) returns (result: seq<real>)
  // No preconditions - hyperbolic cosine is defined for all real numbers
  requires true
  
  ensures |result| == |x|
  
  // Core mathematical definition: cosh(x) = (e^x + e^(-x))/2
  ensures forall i :: 0 <= i < |x| ==>
    result[i] == (Exp(x[i]) + Exp(-x[i])) / 2.0
  
  // Minimum value property: cosh(x) >= 1 for all x
  ensures forall i :: 0 <= i < |x| ==>
    result[i] >= 1.0
  
  // Even function property: cosh(-x) = cosh(x)
  ensures forall i :: 0 <= i < |x| ==>
    (Exp(-x[i]) + Exp(x[i])) / 2.0 == (Exp(x[i]) + Exp(-x[i])) / 2.0
  
  // Monotonicity on non-negative reals: x >= 0 implies cosh(x) >= cosh(0) = 1
  ensures forall i :: 0 <= i < |x| && x[i] >= 0.0 ==>
    result[i] >= 1.0
  
  // Symmetry property: cosh(x) = cosh(|x|)
  ensures forall i :: 0 <= i < |x| ==>
    result[i] == (Exp(Abs(x[i])) + Exp(-Abs(x[i]))) / 2.0
  
  // Identity property: cosh(0) = 1
  ensures forall i :: 0 <= i < |x| && x[i] == 0.0 ==>
    result[i] == 1.0
// </vc-spec>
// <vc-code>
{
  var res := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == (Exp(x[j]) + Exp(-x[j])) / 2.0
    invariant forall j :: 0 <= j < i ==> res[j] >= 1.0
    invariant forall j :: 0 <= j < i ==> res[j] == (Exp(Abs(x[j])) + Exp(-Abs(x[j]))) / 2.0
    invariant forall j :: 0 <= j < i && x[j] == 0.0 ==> res[j] == 1.0
  {
    var cosh_val := (Exp(x[i]) + Exp(-x[i])) / 2.0;
    res := res + [cosh_val];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
