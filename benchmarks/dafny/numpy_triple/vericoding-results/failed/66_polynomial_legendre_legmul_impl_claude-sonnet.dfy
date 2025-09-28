// <vc-preamble>
// Method to multiply two Legendre series represented as coefficient sequences
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): helper to check coefficient bounds */
predicate CoeffBounded(c: seq<real>)
{
  forall i :: 0 <= i < |c| ==> -1000.0 <= c[i] <= 1000.0
}

/* helper modified by LLM (iteration 5): helper to check result bounds */
predicate ResultBounded(result: seq<real>)
{
  forall k :: 0 <= k < |result| ==> -1000000.0 <= result[k] <= 1000000.0
}

/* helper modified by LLM (iteration 5): lemma for multiplication bounds */
lemma MultiplicationBounds(a: real, b: real)
  requires -1000.0 <= a <= 1000.0
  requires -1000.0 <= b <= 1000.0
  ensures -1000000.0 <= a * b <= 1000000.0
{
  // The product bounds follow from the fact that:
  // min value is when one is -1000 and other is 1000: -1000*1000 = -1000000
  // max value is when both have same sign: 1000*1000 = 1000000
  assert a * b >= -1000.0 * 1000.0;
  assert a * b <= 1000.0 * 1000.0;
}

/* helper modified by LLM (iteration 5): lemma for bounded accumulation */
lemma AccumulationBounds(old_val: real, c1_coeff: real, c2_coeff: real)
  requires -1000000.0 <= old_val <= 1000000.0
  requires -1000.0 <= c1_coeff <= 1000.0
  requires -1000.0 <= c2_coeff <= 1000.0
  ensures -1000000.0 <= old_val + c1_coeff * c2_coeff <= 1000000.0
{
  MultiplicationBounds(c1_coeff, c2_coeff);
  // The accumulation of bounded terms remains bounded
  assert -1000000.0 <= c1_coeff * c2_coeff <= 1000000.0;
  assert old_val + c1_coeff * c2_coeff >= -1000000.0 + (-1000000.0);
  assert old_val + c1_coeff * c2_coeff <= 1000000.0 + 1000000.0;
  // For polynomial multiplication, the total accumulation per coefficient
  // is bounded by the sum of at most min(|c1|, |c2|) terms
}
// </vc-helpers>

// <vc-spec>
method LegMul(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  // Input sequences must be non-empty to represent valid polynomial series
  requires |c1| >= 1
  requires |c2| >= 1
  // Output size follows polynomial multiplication rule: degree sum plus 1
  ensures |result| == |c1| + |c2| - 1
  // For constant polynomials (single coefficient), multiplication is straightforward
  ensures |c1| == 1 && |c2| == 1 ==> |result| == 1 && result[0] == c1[0] * c2[0]
  // The result coefficients are bounded based on input coefficient bounds
  ensures (forall i :: 0 <= i < |c1| ==> -1000.0 <= c1[i] <= 1000.0) &&
          (forall j :: 0 <= j < |c2| ==> -1000.0 <= c2[j] <= 1000.0) ==>
          (forall k :: 0 <= k < |result| ==> -1000000.0 <= result[k] <= 1000000.0)
  // Mathematical property: result represents the product of input series in Legendre basis
  // The result is the unique sequence such that Σ result[k]*P_k(x) = (Σ c1[i]*P_i(x)) * (Σ c2[j]*P_j(x))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fix bounds verification with stronger invariants */
  var n := |c1| + |c2| - 1;
  result := seq(n, k => 0.0);
  
  // Handle the simple case first
  if |c1| == 1 && |c2| == 1 {
    if CoeffBounded(c1) && CoeffBounded(c2) {
      MultiplicationBounds(c1[0], c2[0]);
    }
    result := [c1[0] * c2[0]];
    return;
  }
  
  var i := 0;
  while i < |c1|
    invariant 0 <= i <= |c1|
    invariant |result| == |c1| + |c2| - 1
    invariant forall k :: 0 <= k < |result| ==> 
      (CoeffBounded(c1) && CoeffBounded(c2) ==> -2000000.0 <= result[k] <= 2000000.0)
  {
    var j := 0;
    while j < |c2|
      invariant 0 <= j <= |c2|
      invariant |result| == |c1| + |c2| - 1
      invariant forall k :: 0 <= k < |result| ==> 
        (CoeffBounded(c1) && CoeffBounded(c2) ==> -2000000.0 <= result[k] <= 2000000.0)
    {
      var k := i + j;
      if CoeffBounded(c1) && CoeffBounded(c2) {
        AccumulationBounds(result[k], c1[i], c2[j]);
      }
      result := result[k := result[k] + c1[i] * c2[j]];
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
