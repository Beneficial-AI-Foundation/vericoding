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
function ChebNode(i: int, n: int): real
  requires 0 <= i < n
  requires n > 0
  ensures ChebNode(i, n) == Cos(PI * (2.0 * (i as real) + 1.0) / (2.0 * (n as real)))
{
  Cos(PI * (2.0 * (i as real) + 1.0) / (2.0 * (n as real)))
}

lemma NodesAreDistinct(i: int, j: int, n: int)
  requires 0 <= i < n && 0 <= j < n && i != j
  requires n > 0
  ensures ChebNode(i, n) != ChebNode(j, n)
{
  /* helper modified by LLM (iteration 5): Fixed syntax error in trig property */
  var angle_i := PI * (2.0 * (i as real) + 1.0) / (2.0 * (n as real));
  var angle_j := PI * (2.0 * (j as real) + 1.0) / (2.0 * (n as real));
  assert i != j ==> angle_i != angle_j;
}

lemma NodesInOrder(i: int, j: int, n: int)
  requires 0 <= i < j < n
  requires n > 0
  ensures ChebNode(i, n) > ChebNode(j, n)
{
  /* helper modified by LLM (iteration 5): Fixed syntax and added proper bounds */
  var angle_i := PI * (2.0 * (i as real) + 1.0) / (2.0 * (n as real));
  var angle_j := PI * (2.0 * (j as real) + 1.0) / (2.0 * (n as real));
  assert i < j ==> angle_i < angle_j;
  assert 0.0 <= angle_i < angle_j <= PI;
}

lemma NodesInInterval(i: int, n: int)
  requires 0 <= i < n
  requires n > 0
  ensures -1.0 < ChebNode(i, n) < 1.0
{
  /* helper modified by LLM (iteration 5): Added proper bounds on cosine arguments */
  var angle := PI * (2.0 * (i as real) + 1.0) / (2.0 * (n as real));
  assert angle > 0.0;
  assert angle < PI;
}
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
  /* code modified by LLM (iteration 5): Fixed syntax error in loop invariant */
  nodes := [];
  weights := [];
  var i := 0;
  while i < n
    invariant |nodes| == i
    invariant |weights| == i
    invariant forall k :: 0 <= k < i ==> nodes[k] == ChebNode(k, n)
    invariant forall k, l :: 0 <= k < l < i ==> nodes[k] > nodes[l]
    invariant forall k :: 0 <= k < i ==> -1.0 < nodes[k] < 1.0
    invariant forall k, l :: 0 <= k < i && 0 <= l < i && k != l ==> nodes[k] != nodes[l]
    invariant forall k :: 0 <= k < i ==> weights[k] == PI / (n as real)
    invariant i <= n
  {
    nodes := nodes + [ChebNode(i, n)];
    weights := weights + [PI / (n as real)];
    i := i + 1;
  }
}
// </vc-code>
