// <vc-preamble>
// Method to multiply two Legendre series represented as coefficient sequences
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 3): Implemented polynomial multiplication by summing coefficients over indices where i+j equals position, ensuring sequence length and bounds with loop invariants */
  var resultSeq: seq<real> := seq(|c1| + |c2| - 1, i => 0.0);
  for i : int := 0 to |c1| - 1
    invariant 0 <= i <= |c1|
    invariant |resultSeq| == |c1| + |c2| - 1
  {
    for j : int := 0 to |c2| - 1
      invariant 0 <= j <= |c2|
      invariant |resultSeq| == |c1| + |c2| - 1
    {
      var k := i + j;
      resultSeq := resultSeq[k := resultSeq[k] + c1[i] * c2[j]];
    }
  }
  result := resultSeq;
}
// </vc-code>
