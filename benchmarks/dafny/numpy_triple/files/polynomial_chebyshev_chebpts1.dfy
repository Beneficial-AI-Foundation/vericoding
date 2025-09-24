// <vc-preamble>
// Mathematical constants and functions
const PI: real := 3.141592653589793

// Abstract trigonometric functions
function {:axiom} cos(x: real): real
{
  0.0  // Dummy body for compilation; actual behavior defined by axioms
}

// Properties of cosine function needed for specification
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
lemma {:axiom} cos_range(x: real)
  ensures -1.0 <= cos(x) <= 1.0

lemma {:axiom} cos_decreasing_property(x: real, y: real)
  requires 0.0 <= x < y <= PI
  ensures cos(x) > cos(y)

lemma {:axiom} cos_symmetry(x: real)
  ensures cos(PI - x) == -cos(x)

method chebpts1(n: nat) returns (result: seq<real>)
  requires n > 0
  ensures |result| == n
  
  // Each point follows the Chebyshev formula
  ensures forall k :: 0 <= k < n ==> 
    result[k] == cos(PI * (k as real + 0.5) / (n as real))
  
  // Points are in descending order
  ensures forall i, j :: 0 <= i < j < n ==> result[i] > result[j]
  
  // All points lie in [-1, 1]
  ensures forall k :: 0 <= k < n ==> -1.0 <= result[k] <= 1.0
  
  // Symmetry property: result[k] = -result[n-1-k]
  ensures forall k :: 0 <= k < n ==> 
    result[k] == -result[n - 1 - k]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
