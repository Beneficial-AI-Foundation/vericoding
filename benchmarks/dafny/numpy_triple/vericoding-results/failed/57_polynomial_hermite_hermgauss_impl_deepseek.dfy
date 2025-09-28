// <vc-preamble>
// Helper function to compute the sum of a sequence of reals
function Sum(s: seq<real>): real
{
    if |s| == 0 then 0.0
    else s[0] + Sum(s[1..])
}

// Method to compute Gauss-Hermite quadrature points and weights
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed comprehension syntax removing 'in' keyword */
function Factorial(n: nat): nat
  decreases n
{
  if n == 0 then 1 else n * Factorial(n - 1)
}

function HermitePolynomial(n: nat, x: real): real
  decreases n
{
  if n == 0 then 1.0
  else if n == 1 then 2.0 * x
  else 2.0 * x * HermitePolynomial(n - 1, x) - 2.0 * (n - 1) * HermitePolynomial(n - 2, x)
}

function HermitePolynomialDerivative(n: nat, x: real): real
  decreases n
{
  if n == 0 then 0.0
  else if n == 1 then 2.0
  else 2.0 * HermitePolynomial(n - 1, x) + 2.0 * x * HermitePolynomialDerivative(n - 1, x) - 2.0 * (n - 1) * HermitePolynomialDerivative(n - 2, x)
}

function NewtonRaphson(n: nat, x0: real, tolerance: real, max_iter: nat): (x1: real)
  requires tolerance > 0.0
  requires max_iter > 0
  requires HermitePolynomialDerivative(n, x0) != 0.0
  decreases max_iter
{
  if max_iter == 0 then x0
  else
    var f := HermitePolynomial(n, x0);
    var f_prime := HermitePolynomialDerivative(n, x0);
    if f_prime == 0.0 then x0 else
    var x1 := x0 - f / f_prime;
    if |x1 - x0| < tolerance then x1
    else NewtonRaphson(n, x1, tolerance, max_iter - 1)
}

function ComputeWeight(n: nat, x: real): real
{
  2.0^(n - 1) * Factorial(n) * Math.sqrt(Math.PI) / (n * n * HermitePolynomial(n - 1, x) * HermitePolynomial(n - 1, x))
}

function QuickSort(s: seq<real>): (result: seq<real>)
  ensures |s| == |result|
{
  if |s| <= 1 then s
  else
    var pivot := s[0];
    var left := QuickSort([x | x in s[1..], x <= pivot]);
    var right := QuickSort([x | x in s[1..], x > pivot]);
    left + [pivot] + right
}

function FindIndex(s: seq<real>, value: real): (index: nat)
  requires value in s
  ensures index < |s| && s[index] == value
{
  if s[0] == value then 0
  else 1 + FindIndex(s[1..], value)
}
// </vc-helpers>

// <vc-spec>
method hermgauss(deg: nat) returns (points: seq<real>, weights: seq<real>)
    requires deg > 0
    ensures |points| == deg
    ensures |weights| == deg
    // All weights are positive
    ensures forall i :: 0 <= i < deg ==> weights[i] > 0.0
    // Weights sum to a positive value
    ensures Sum(weights) > 0.0
    // Points are symmetric around 0 (for each point there's a negative counterpart)
    ensures forall i :: 0 <= i < deg ==> exists j :: 0 <= j < deg && points[i] == -points[j]
    // Points are distinct
    ensures forall i, j :: 0 <= i < deg && 0 <= j < deg && i != j ==> points[i] != points[j]
    // Points are sorted in ascending order
    ensures forall i, j :: 0 <= i < deg && 0 <= j < deg && i < j ==> points[i] < points[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed Dafny syntax error in filtering expressions */
  const tolerance := 1.0E-10;
  var max_iterations := 100;
  var n := deg;
  
  points := [];
  weights := [];
  
  if n % 2 == 1 {
    var root := NewtonRaphson(n, 0.0, tolerance, max_iterations);
    var weight := ComputeWeight(n, root);
    points := points + [root];
    weights := weights + [weight];
  }
  
  var i: int := n / 2 - 1;
  while i >= 0
    decreases i + 1
  {
    var initial_guess: real := 1.0 + i * 1.5;
    var root := NewtonRaphson(n, initial_guess, tolerance, max_iterations);
    var weight := ComputeWeight(n, root);
    
    points := [root] + points;
    points := points + [-root];
    weights := [weight] + weights;
    weights := weights + [weight];
    
    i := i - 1;
  }
  
  var sorted_points := QuickSort(points);
  var sorted_weights := [];
  
  var j: nat := 0;
  while j < |sorted_points|
    decreases |sorted_points| - j
  {
    var idx := FindIndex(points, sorted_points[j]);
    sorted_weights := sorted_weights + [weights[idx]];
    j := j + 1;
  }
  
  points := sorted_points;
  weights := sorted_weights;
}
// </vc-code>
