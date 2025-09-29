// <vc-preamble>
/*
 * Dafny specification for extracting imaginary parts of complex numbers.
 * Translates numpy.imag functionality that returns the imaginary component
 * of complex arguments represented as (real, imaginary) pairs.
 */

// Helper function for complex addition
function ComplexAdd(z1: (real, real), z2: (real, real)): (real, real)
{
  (z1.0 + z2.0, z1.1 + z2.1)
}

// Helper function for scalar multiplication of complex numbers
function ComplexScale(scalar: real, z: (real, real)): (real, real)
{
  (scalar * z.0, scalar * z.1)
}

// Helper function for complex conjugate
function ComplexConj(z: (real, real)): (real, real)
{
  (z.0, -z.1)
}

// Method to extract imaginary parts from a sequence of complex numbers
// Each complex number is represented as a pair (real, imaginary)
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Imag(val: seq<(real, real)>) returns (result: seq<real>)
  // Output sequence has same length as input sequence
  ensures |result| == |val|
  
  // Each element in result is the imaginary part of corresponding input element
  ensures forall i :: 0 <= i < |val| ==> result[i] == val[i].1
  
  // Linearity property: imag preserves scalar multiplication
  ensures forall i :: 0 <= i < |val| ==> forall scalar: real ::
    var scaled := ComplexScale(scalar, val[i]);
    scalar * result[i] == scaled.1
    
  // Additive property: imag(z₁ + z₂) = imag(z₁) + imag(z₂)
  ensures forall i, j :: 0 <= i < |val| && 0 <= j < |val| ==>
    var sum := ComplexAdd(val[i], val[j]);
    result[i] + result[j] == sum.1
    
  // Conjugate property: imag(conj(z)) = -imag(z)
  ensures forall i :: 0 <= i < |val| ==>
    var conj := ComplexConj(val[i]);
    -result[i] == conj.1
// </vc-spec>
// <vc-code>
{
  result := [];
  for i := 0 to |val|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == val[j].1
  {
    result := result + [val[i].1];
  }
}
// </vc-code>
