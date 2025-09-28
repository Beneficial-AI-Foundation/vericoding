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
  /* code modified by LLM (iteration 5): strengthened loop invariants for bounds proof */
  var n := |c1| + |c2| - 1;
  result := [];
  
  if |c1| == 1 && |c2| == 1 {
    result := [c1[0] * c2[0]];
    return;
  }
  
  var k := 0;
  
  while k < n
    invariant 0 <= k <= n
    invariant |result| == k
    invariant forall idx :: 0 <= idx < k ==>
      ((forall ii :: 0 <= ii < |c1| ==> -1000.0 <= c1[ii] <= 1000.0) &&
       (forall jj :: 0 <= jj < |c2| ==> -1000.0 <= c2[jj] <= 1000.0)) ==> 
      -1000000.0 <= result[idx] <= 1000000.0
  {
    var sum := 0.0;
    var i := 0;
    var minIdx := if k >= |c2| then k - |c2| + 1 else 0;
    var maxIdx := if k < |c1| then k + 1 else |c1|;
    
    while i < |c1| && i <= k
      invariant 0 <= i <= |c1|
      invariant i <= k + 1
      invariant (forall ii :: 0 <= ii < |c1| ==> -1000.0 <= c1[ii] <= 1000.0) &&
                (forall jj :: 0 <= jj < |c2| ==> -1000.0 <= c2[jj] <= 1000.0) ==> 
                -1000000.0 * (maxIdx as real) <= sum && sum <= 1000000.0 * (maxIdx as real)
    {
      if k - i >= 0 && k - i < |c2| {
        sum := sum + c1[i] * c2[k - i];
      }
      i := i + 1;
    }
    
    result := result + [sum];
    k := k + 1;
  }
}
// </vc-code>
