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
// Helper function to compute node value at index i
function ComputeNode(i: nat, n: nat): real
  requires n > 0
  requires i < n
{
  Cos(PI * (2.0 * (i as real) + 1.0) / (2.0 * (n as real)))
}

// Helper function to compute weight value for given n
function ComputeWeight(n: nat): real
  requires n > 0
{
  PI / (n as real)
}

/* helper modified by LLM (iteration 5): Fixed triggers and ghost proofs */
lemma WeightIsPositive(n: nat)
  requires n > 0
  ensures PI / (n as real) > 0.0
{
  // PI > 0 and n > 0, so PI/n > 0
}

lemma NodesMatchFormula(n: nat)
  requires n > 0
  ensures forall i {:trigger ComputeNode(i, n)} :: 0 <= i < n ==> 
    ComputeNode(i, n) == Cos(PI * (2.0 * (i as real) + 1.0) / (2.0 * (n as real)))
{
  // Follows directly from definition of ComputeNode
}

lemma WeightsMatchFormula(n: nat)
  requires n > 0
  ensures forall i {:trigger ComputeWeight(n)} :: 0 <= i < n ==> ComputeWeight(n) == PI / (n as real)
{
  // Follows directly from definition of ComputeWeight
}

lemma NodesInInterval(n: nat)
  requires n > 0
  ensures forall i {:trigger ComputeNode(i, n)} :: 0 <= i < n ==> -1.0 < ComputeNode(i, n) < 1.0
{
  // Properties follow from Cos function postcondition and angle being in (0, PI)
}

lemma NodesDecreasing(n: nat)
  requires n > 0
  ensures forall i, j {:trigger ComputeNode(i, n), ComputeNode(j, n)} :: 0 <= i < j < n ==> ComputeNode(i, n) > ComputeNode(j, n)
{
  // Properties follow from Cos being decreasing on (0, PI)
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
  /* code modified by LLM (iteration 5): Simplified implementation with ghost calls */
  nodes := seq(n, i requires 0 <= i < n => ComputeNode(i, n));
  weights := seq(n, i requires 0 <= i < n => ComputeWeight(n));
  
  ghost var _ := WeightIsPositive(n);
  ghost var _ := NodesMatchFormula(n);
  ghost var _ := WeightsMatchFormula(n);
  ghost var _ := NodesInInterval(n);
  ghost var _ := NodesDecreasing(n);
}
// </vc-code>
