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
/* helper modified by LLM (iteration 2): recursive builder for convolution sequence without seq comprehension */
function BuildConv(a: seq<real>, v: seq<real>, n: int): seq<real>
  requires |a| > 0 && |v| > 0
  requires 0 <= n <= |a| + |v| - 1
  decreases n
{
  if n == 0 then []
  else BuildConv(a, v, n - 1) + [ConvolutionSum(a, v, n - 1)]
}

/* helper modified by LLM (iteration 2): wrapper to produce full convolution result */
function ConvolutionResult(a: seq<real>, v: seq<real>): seq<real>
  requires |a| > 0 && |v| > 0
{
  BuildConv(a, v, |a| + |v| - 1)
}

/* helper modified by LLM (iteration 2): lemma for edge cases of convolution sum */
lemma ConvEdgeLemma(a: seq<real>, v: seq<real>)
  requires |a| > 0 && |v| > 0
  ensures ConvolutionSum(a, v, 0) == a[0] * v[0]
  ensures ConvolutionSum(a, v, |a| + |v| - 2) == a[|a| - 1] * v[|v| - 1]
{
  // First element k = 0
  assert MaxInt(0, 0 - |v| + 1) == 0;
  assert MinInt(|a| - 1, 0) == 0;
  assert 0 <= 0 < |a|;
  assert 0 <= 0 - 0 < |v|;
  assert ConvolutionSum(a, v, 0) == SumOverRange(a, v, 0, 0, 0);
  assert SumOverRange(a, v, 0, 0, 0) == a[0] * v[0];

  // Last element k = |a| + |v| - 2
  var L := |a| + |v| - 1;
  assert MaxInt(0, (L - 1) - |v| + 1) == |a| - 1;
  assert MinInt(|a| - 1, L - 1) == |a| - 1;
  assert 0 <= |a| - 1 < |a|;
  assert 0 <= (L - 1) - (|a| - 1) < |v|;
  assert ConvolutionSum(a, v, L - 1) == SumOverRange(a, v, L - 1, |a| - 1, |a| - 1);
  assert SumOverRange(a, v, L - 1, |a| - 1, |a| - 1) == a[|a| - 1] * v[|v| - 1];
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
{
  /* code modified by LLM (iteration 2): iterative construction with invariants and edge lemma */
  var L := |a| + |v| - 1;
  ConvEdgeLemma(a, v);

  var r: seq<real> := [];
  var i: int := 0;
  while i < L
    invariant 0 <= i <= L
    invariant |r| == i
    invariant forall k :: 0 <= k < i ==> r[k] == ConvolutionSum(a, v, k)
    decreases L - i
  {
    r := r + [ConvolutionSum(a, v, i)];
    i := i + 1;
  }
  result := r;
  assert |result| == L;
  if L > 0 {
    assert result[0] == ConvolutionSum(a, v, 0);
    assert ConvolutionSum(a, v, 0) == a[0] * v[0];
    assert result[|result| - 1] == ConvolutionSum(a, v, L - 1);
    assert ConvolutionSum(a, v, L - 1) == a[|a| - 1] * v[|v| - 1];
  }
}
// </vc-code>
