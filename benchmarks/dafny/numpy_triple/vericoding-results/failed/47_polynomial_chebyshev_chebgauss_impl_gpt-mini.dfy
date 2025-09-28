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
/* helper modified by LLM (iteration 5): Angle computes the angle for node i */
function Angle(n: nat, i: nat): real
  requires i < n
  ensures Angle(n,i) == PI * (2.0 * (i as real) + 1.0) / (2.0 * (n as real))
{
  PI * (2.0 * (i as real) + 1.0) / (2.0 * (n as real))
}

/* helper modified by LLM (iteration 5): prove angle lies in (0,PI) */
lemma AngleInInterval(n: nat, i: nat)
  requires 0 < n && i < n
  ensures 0.0 < Angle(n,i) < PI
{
  // Work with integer bounds to get a strict inequality for the fraction
  var numInt := 2 * i + 1;
  var denInt := 2 * n;
  // i < n implies i + 1 <= n (integers)
  assert i + 1 <= n;
  // therefore 2*i + 1 <= 2*(n-1) + 1 = 2*n - 1 = denInt - 1
  assert 2 * i + 1 <= 2 * (n - 1) + 1;
  assert 2 * (n - 1) + 1 == denInt - 1;
  assert 2 * i + 1 <= denInt - 1;
  // hence strict inequality between numerator and denominator
  assert 2 * i + 1 < denInt;

  var num := (numInt as real);
  var den := (denInt as real);
  assert num == 2.0 * (i as real) + 1.0;
  assert den == 2.0 * (n as real);
  // fraction in (0,1)
  assert 0.0 < num;
  assert num < den;
  assert 0.0 < num / den;
  assert num / den < 1.0;
  // relate to Angle and multiply by positive PI
  assert Angle(n,i) == PI * (num / den);
  assert 0.0 < PI * (num / den) < PI;
}

/* helper modified by LLM (iteration 5): weights positivity */
lemma WeightsPositive(n: nat)
  requires n > 0
  ensures PI / (n as real) > 0.0
{
  assert PI > 0.0;
  assert (n as real) > 0.0;
  assert PI / (n as real) > 0.0;
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
/* code modified by LLM (iteration 5): fill arrays with nodes and weights and call lemmas to establish angle properties */
{
  var nodesArr := new real[n];
  var weightsArr := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> nodesArr[k] == Cos(Angle(n,k))
    invariant forall k :: 0 <= k < i ==> weightsArr[k] == PI / (n as real)
    decreases n - i
  {
    var angle := Angle(n, i);
    // establish the angle lies in (0,PI) for this index to help verification
    AngleInInterval(n, i);
    nodesArr[i] := Cos(angle);
    weightsArr[i] := PI / (n as real);
    i := i + 1;
  }
  // establish weights positivity for the whole array
  WeightsPositive(n);
  nodes := nodesArr[..];
  weights := weightsArr[..];
}

// </vc-code>
