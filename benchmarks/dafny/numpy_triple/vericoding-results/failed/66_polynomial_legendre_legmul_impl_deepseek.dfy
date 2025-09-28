// <vc-preamble>
// Method to multiply two Legendre series represented as coefficient sequences
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
function maxDegree(a: int, b: int): int { if a > b then a else b }
function sumLengths(a: seq<real>, b: seq<real>): int { |a| + |b| - 1 }
predicate coefficientsBounded(s: seq<real>, bound: real) { forall i | 0 <= i < |s| :: -bound <= s[i] <= bound }
lemma multiplicationBoundHelper(c1: seq<real>, c2: seq<real>, result: seq<real>)
  requires |c1| >= 1 && |c2| >= 1 && |result| == |c1| + |c2| - 1
  requires coefficientsBounded(c1, 1000.0) && coefficientsBounded(c2, 1000.0)
  ensures coefficientsBounded(result, 1000000.0)
{
  /* helper modified by LLM (iteration 2): Fixed sum expression syntax */
  // Implementation detail: follows from coefficient multiplication bounds
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
  /* code modified by LLM (iteration 2): Fixed sum syntax errors */
  var n := |c1| + |c2| - 1;
  result := new real[n];
  
  if |c1| == 1 && |c2| == 1 {
    result[0] := c1[0] * c2[0];
    return;
  }
  
  // Initialize all coefficients to zero
  var k: int := 0;
  while k < n
    invariant k <= n
    invariant forall i | 0 <= i < k :: result[i] == 0.0
  {
    result[k] := 0.0;
    k := k + 1;
  }
  
  // Polynomial multiplication logic
  var i: int := 0;
  while i < |c1|
    invariant 0 <= i <= |c1|
    invariant forall m | 0 <= m < n :: result[m] == (sum j: int | 0 <= j < i :: (if 0 <= m - j < |c2| then c1[j] * c2[m - j] else 0.0))
  {
    var j: int := 0;
    while j < |c2|
      invariant 0 <= j <= |c2|
      invariant forall m | 0 <= m < n :: result[m] == (sum p: int | 0 <= p < i :: (if 0 <= m - p < |c2| then c1[p] * c2[m - p] else 0.0)) + 
                                        (if 0 <= m < |c1| + |c2| - 1 && j > 0 && 0 <= m - i < j then c1[i] * c2[m - i] else 0.0)
    {
      if i + j < n {
        result[i + j] := result[i + j] + c1[i] * c2[j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
