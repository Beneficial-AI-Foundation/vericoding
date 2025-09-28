// <vc-preamble>
/*
 * Calculate exp(x) - 1 for all elements in the vector.
 * This function provides greater precision than exp(x) - 1 for small values of x.
 * Implements element-wise expm1 computation with enhanced numerical precision.
 */

// Mathematical function declarations for specification
function Exp(x: real): real
{
  1.0 + x // Placeholder implementation for compilation
}

function Abs(x: real): real
  ensures Abs(x) >= 0.0
  ensures x >= 0.0 ==> Abs(x) == x
  ensures x < 0.0 ==> Abs(x) == -x
{
  if x >= 0.0 then x else -x
}

// Main expm1 method that computes exp(x) - 1 element-wise with enhanced precision
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed termination with decreases clause, simplified to match specification */
function ExpHelper(x: real): real
  ensures x >= 0.0 ==> ExpHelper(x) >= 1.0
  ensures x <= 0.0 ==> ExpHelper(x) <= 1.0
  ensures ExpHelper(0.0) == 1.0
  ensures forall x,y :: x <= y ==> ExpHelper(x) <= ExpHelper(y)
decreases Abs(x)
{
  if x <= 0.0 then 1.0 / (1.0 - x + x*x/2.0) else 1.0 + x + x*x/2.0 + x*x*x/6.0
}

predicate IsMonotonicIncreasing(s: seq<real>)
{
  forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma ExpM1Lemma(x: real)
  ensures ExpHelper(x) - 1.0 > -1.0
  ensures x == 0.0 ==> ExpHelper(x) - 1.0 == 0.0
  ensures x > 0.0 ==> ExpHelper(x) - 1.0 > x
  ensures Abs(x) <= 1.0 ==> ((x > 0.0 ==> ExpHelper(x) - 1.0 > 0.0) && (x < 0.0 ==> ExpHelper(x) - 1.0 < 0.0))
  ensures Abs(x) <= 0.1 ==> Abs((ExpHelper(x) - 1.0) - x) <= Abs(x)*Abs(x)
{
}
// </vc-helpers>

// <vc-spec>
method Expm1(x: seq<real>) returns (result: seq<real>)
  // Output vector has same length as input
  ensures |result| == |x|
  // For each element i in the vectors, all mathematical properties hold
  ensures forall i :: 0 <= i < |x| ==> (
    // Basic mathematical property: result equals exp(x) - 1
    result[i] == Exp(x[i]) - 1.0 &&
    // Monotonicity property: expm1 is strictly increasing across elements
    (forall j :: 0 <= j < |x| && x[i] < x[j] ==> result[i] < result[j]) &&
    // Identity property: expm1(0) = 0
    (x[i] == 0.0 ==> result[i] == 0.0) &&
    // Asymptotic behavior for small values: exp(x) - 1 ≈ x for small x
    (Abs(x[i]) <= 0.1 ==> Abs(result[i] - x[i]) <= Abs(x[i]) * Abs(x[i])) &&
    // Sign preservation for small values
    (Abs(x[i]) <= 1.0 ==> ((x[i] > 0.0 ==> result[i] > 0.0) && (x[i] < 0.0 ==> result[i] < 0.0))) &&
    // Lower bound for positive values: expm1(x) > x for x > 0
    (x[i] > 0.0 ==> result[i] > x[i]) &&
    // Upper bound for all values: expm1(x) > -1 for all x
    result[i] > -1.0
  )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use proper Exp function instead of ExpHelper to match specification */
{
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == Exp(x[j]) - 1.0
  {
    result := result + [Exp(x[i]) - 1.0];
    i := i + 1;
  }
  // Call lemma to help prove properties
  ExpM1Lemma(0.0);
}
// </vc-code>
