// <vc-preamble>
/*
 * Gauss-Chebyshev quadrature computation
 * 
 * This file provides a specification for computing Gauss-Chebyshev quadrature
 * nodes and weights. The nodes are zeros of Chebyshev polynomials and weights
 * are uniform, used for numerical integration over [-1,1] with weight function
 * 1/√(1-x²).
 */

// Mathematical constants and functions needed for the specification
const PI: real := 3.141592653589793

// Cosine function (ghost function for specification purposes)
function {:extern} {:axiom} Cos(x: real): real
  ensures -1.0 <= Cos(x) <= 1.0

// Main method for computing Gauss-Chebyshev quadrature nodes and weights
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ChebGauss(n: nat) returns (nodes: seq<real>, weights: seq<real>)
  requires n > 0
  ensures |nodes| == n
  ensures |weights| == n
  // Nodes follow Chebyshev-Gauss quadrature formula: x_i = cos(π(2i+1)/(2n))
  ensures forall i :: 0 <= i < n ==> 
    nodes[i] == Cos(PI * (2.0 * (i as real) + 1.0) / (2.0 * (n as real)))
  // All weights are equal to π/n
  ensures forall i :: 0 <= i < n ==> weights[i] == PI / (n as real)
  // Weights are positive
  ensures forall i :: 0 <= i < n ==> weights[i] > 0.0
  // Nodes are in descending order (cosine is decreasing on [0,π])
  ensures forall i, j :: 0 <= i < j < n ==> nodes[i] > nodes[j]
  // All nodes are in the open interval (-1, 1)
  ensures forall i :: 0 <= i < n ==> -1.0 < nodes[i] < 1.0
  // All nodes are distinct
  ensures forall i, j :: 0 <= i < n && 0 <= j < n && i != j ==> nodes[i] != nodes[j]
// </vc-spec>
// <vc-code>

{
  /* code modified by LLM (iteration 5): retained the loop implementation from iteration 4, but the invariants for descending order and strict range remain unprovable due to limitations in extern Cos specification */
  nodes := [];
  weights := [];
  var i : nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |nodes| == i
    invariant |weights| == i
    invariant forall k ::  سخت 0 <= k < i ==> 
      nodes[k] == Cos(PI * (2.0 * (k as real) + 1.0) / ( hyp 2.0 * (n as real)))
    invariant forall k :: 0 <= k < i ==> weights[k] == PI / (n as real)
    invariant forall k, m :: 0 <= k < m < i ==> nodes[k] > nodes[m]
    invariant forall k :: 0 <= k < i ==> -1.0 < nodes[k] < 1.0
  {
    nodes := nodes + [Cos(PI * (2.0 * (i as real) + 1.0) / (2.0 * (n as real)))];
    weights := weights + [PI / (n as real)];
    i := i + 1;
  }
}
// </vc-code>
