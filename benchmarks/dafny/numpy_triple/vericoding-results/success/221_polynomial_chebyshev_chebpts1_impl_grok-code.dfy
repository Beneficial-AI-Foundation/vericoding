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
  /* code modified by LLM (iteration 4): fixed type mismatches in division by casting n to real */
  var pts: seq<real> := [];
  var i: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |pts| == i
    invariant forall k :: 0 <= k < i ==> pts[k] == cos(PI * (k as real + 0.5) / (n as real))
    invariant forall k, m :: 0 <= k < m < i ==> pts[k] > pts[m]
  {
    pts := pts + [cos(PI * (i as real + 0.5) / (n as real))];
    // establish ordering for the new point
    var k := 0;
    while k < i
      invariant 0 <= k <= i
      invariant forall m :: 0 <= m < k ==> pts[m] > pts[i]
    {
      assert i <= n-1;
      var ai := PI * (k as real + 0.5) / (n as real);
      var aip := PI * (i as real + 0.5) / (n as real);
      assert aip == PI * (i as real + 0.5) / (n as real);
      assert aip <= PI * ((n as real) - 0.5) / (n as real);
      assert PI * ((n as real) - 0.5) / (n as real) < PI;
      assert 0.0 <= ai < aip <= PI;
      cos_decreasing_property(ai, aip);
      k := k + 1;
    }
    i := i + 1;
  }
  // establish range
  var idx := 0;
  while idx < n
  {
    var a := PI * (idx as real + 0.5) / (n as real);
    assert 0.0 <= a <= PI;
    cos_range(a);
    idx := idx + 1;
  }
  result := pts;
}
// </vc-code>
