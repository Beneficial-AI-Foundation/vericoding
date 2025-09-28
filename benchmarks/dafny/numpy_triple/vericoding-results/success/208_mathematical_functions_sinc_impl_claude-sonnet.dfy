// <vc-preamble>
// Ghost functions for mathematical operations (axiomatized)
function {:axiom} RealSin(x: real): real
{
    0.0  // Placeholder implementation for compilation
}

function {:axiom} RealPi(): real
    ensures RealPi() > 3.14 && RealPi() < 3.15
{
    3.141592653589793  // Placeholder implementation for compilation
}

// Helper function to define the mathematical sinc function
function SincValue(x: real): real
{
    if x == 0.0 then 1.0
    else (RealSin(RealPi() * x)) / (RealPi() * x)
}

// Main method specification for element-wise sinc computation
// Helper predicate to check if a real number is an integer
ghost predicate IsInteger(x: real)
{
    exists k: int {:trigger k as real} :: x == k as real
}
// </vc-preamble>

// <vc-helpers>
// Helper lemma to establish symmetry property of SincValue
lemma SincSymmetry(a: real)
    ensures SincValue(-a) == SincValue(a)
{
    if a == 0.0 {
        // SincValue(0) == SincValue(-0) == 1.0
        assert SincValue(-a) == 1.0 == SincValue(a);
    } else {
        // For non-zero a, both expressions evaluate to sin(pi*a)/(pi*a)
        // since sin(-x) = -sin(x) and (-a) appears in both numerator and denominator
        assert -a != 0.0;
        assert SincValue(-a) == (RealSin(RealPi() * (-a))) / (RealPi() * (-a));
        assert SincValue(a) == (RealSin(RealPi() * a)) / (RealPi() * a);
    }
}
// </vc-helpers>

// <vc-spec>
method Sinc(x: seq<real>) returns (result: seq<real>)
    // No preconditions needed - sinc is defined for all real numbers
    ensures |result| == |x|
    // Element-wise computation: each result[i] equals sinc of x[i]
    ensures forall i :: 0 <= i < |x| ==> result[i] == SincValue(x[i])
    // Maximum at zero: sinc(0) = 1
    ensures forall i :: 0 <= i < |x| && x[i] == 0.0 ==> result[i] == 1.0
    // Symmetry property: sinc(-x) = sinc(x) for corresponding elements
    ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && x[i] == -x[j] ==> result[i] == result[j]
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == SincValue(x[j])
  {
    var sinc_val := SincValue(x[i]);
    result := result + [sinc_val];
    i := i + 1;
  }
}
// </vc-code>
