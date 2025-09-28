// <vc-preamble>
/*
 * Implementation of the Legendre polynomial weight function.
 * The weight function for Legendre polynomials is constant 1 over the interval [-1, 1].
 * This module provides a method to compute the weight function values for given input points.
 */

// Method to compute the Legendre polynomial weight function
// The weight function is constant 1 for all input values
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove array slice elements are ones */
lemma ArrayAllOnesImpliesSeqAllOnes(a: array<real>)
  requires forall i :: 0 <= i < a.Length ==> a[i] == 1.0
  ensures forall i :: 0 <= i < a.Length ==> a[..][i] == 1.0
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[..][j] == 1.0
  {
    assert a[i] == 1.0;
    assert a[..][i] == 1.0;
    i := i + 1;
  }
}

// </vc-helpers>

// <vc-spec>
method legweight(x: seq<real>) returns (result: seq<real>)
  // No preconditions - the weight function is defined for all real values
  requires true
  // The output vector has the same length as the input vector
  ensures |result| == |x|
  // All elements in the result are 1.0, representing the constant weight function
  ensures forall i :: 0 <= i < |result| ==> result[i] == 1.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fill array with ones and return as seq */
  var n := |x|;
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == 1.0
  {
    a[i] := 1.0;
    i := i + 1;
  }
  result := a[..];
}

// </vc-code>
