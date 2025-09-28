// <vc-preamble>
// Helper function to compute the sum of products for convolution at position k
function ConvolutionSum(a: seq<real>, v: seq<real>, k: int): real
  requires |a| > 0 && |v| > 0
  requires 0 <= k < |a| + |v| - 1
{
  // Sum over all valid indices i where both a[i] and v[k-i] exist
  SumOverRange(a, v, k, MaxInt(0, k - |v| + 1), MinInt(|a| - 1, k))
}

// Recursive helper to compute sum over a range of indices
function SumOverRange(a: seq<real>, v: seq<real>, k: int, start: int, end: int): real
  requires |a| > 0 && |v| > 0
  requires 0 <= k < |a| + |v| - 1
  requires start <= end + 1
  decreases end - start + 1
{
  if start > end then 0.0
  else if start == end then 
    if 0 <= start < |a| && 0 <= k - start < |v| then
      a[start] * v[k - start]
    else 0.0
  else
    (if 0 <= start < |a| && 0 <= k - start < |v| then a[start] * v[k - start] else 0.0) +
    SumOverRange(a, v, k, start + 1, end)
}

// Utility functions for max and min
function MaxInt(x: int, y: int): int { if x >= y then x else y }
function MinInt(x: int, y: int): int { if x <= y then x else y }

// Main convolution method
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma to verify convolution sum matches ConvolutionSum */
lemma ConvolutionSumLemma(a: seq<real>, v: seq<real>, k: int)
  requires |a| > 0 && |v| > 0
  requires 0 <= k < |a| + |v| - 1
  ensures ConvolutionSum(a, v, k) == (
    var start := MaxInt(0, k - |v| + 1);
    var end := MinInt(|a| - 1, k);
    SumOverRange(a, v, k, start, end)
  )
{
}

// Helper lemma to verify the base case of SumOverRange
lemma SumOverRangeBaseCase(a: seq<real>, v: seq<real>, k: int, i: int)
  requires |a| > 0 && |v| > 0
  requires 0 <= k < |a| + |v| - 1
  requires 0 <= i < |a| && 0 <= k - i < |v|
  ensures SumOverRange(a, v, k, i, i) == a[i] * v[k - i]
{
}

// Helper lemma to verify the recursive case of SumOverRange
lemma SumOverRangeRecursive(a: seq<real>, v: seq<real>, k: int, start: int, end: int)
  requires |a| > 0 && |v| > 0
  requires 0 <= k < |a| + |v| - 1
  requires start <= end
  requires start + 1 <= end + 1
  decreases end - start
  ensures SumOverRange(a, v, k, start, end) == 
    (if 0 <= start < |a| && 0 <= k - start < |v| then a[start] * v[k - start] else 0.0) +
    SumOverRange(a, v, k, start + 1, end)
{
}
// </vc-helpers>

// <vc-spec>
method numpy_convolve(a: seq<real>, v: seq<real>) returns (result: seq<real>)
  // Precondition: Both input vectors must be non-empty
  requires |a| > 0 && |v| > 0
  
  // Postcondition: Result length is m + n - 1
  ensures |result| == |a| + |v| - 1
  
  // Postcondition: Each element follows the convolution definition
  ensures forall k :: 0 <= k < |result| ==> 
    result[k] == ConvolutionSum(a, v, k)
  
  // Postcondition: Edge case - first element
  ensures result[0] == a[0] * v[0]
  
  // Postcondition: Edge case - last element  
  ensures result[|result| - 1] == a[|a| - 1] * v[|v| - 1]
  
  // Postcondition: Mathematical property - convolution preserves finite values
  ensures forall k :: 0 <= k < |result| ==> result[k] == result[k]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed array/seq type mismatch and result assignment */
{
  var length := |a| + |v| - 1;
  result := [];
  
  var k := 0;
  while k < length
    invariant 0 <= k <= length
    invariant |result| == k
    invariant forall i :: 0 <= i < k ==> result[i] == ConvolutionSum(a, v, i)
  {
    var start := MaxInt(0, k - |v| + 1);
    var end := MinInt(|a| - 1, k);
    
    result := result + [SumOverRange(a, v, k, start, end)];
    
    k := k + 1;
  }
}
// </vc-code>
