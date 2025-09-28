// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Replaced helper functions with proper sequence operations */
function poly_length(c: seq<real>): int
  ensures poly_length(c) == |c| + 1
{
  |c| + 1
}

function poly_element(k: int, c: seq<real>): real
  requires 0 <= k < |c| + 1
  ensures poly_element(k, c) == (if k > 0 && k-1 < |c| then c[k-1] / 2.0 else 0.0) + (if k+1 < |c| then c[k+1] * (k+1) as real else 0.0)
{
  (if k > 0 && k-1 < |c| then c[k-1] / 2.0 else 0.0) + (if k+1 < |c| then c[k+1] * (k+1) as real else 0.0)
}
// </vc-helpers>

// <vc-spec>
method hermmulx(c: seq<real>) returns (result: seq<real>)
  requires |c| >= 0
  ensures |result| == |c| + 1
  ensures forall k :: 0 <= k < |result| ==>
    result[k] == 
      // Contribution from c[k-1]/2 when k > 0 and k-1 < |c|
      (if k > 0 && k-1 < |c| then c[k-1] / 2.0 else 0.0) +
      // Contribution from c[k+1]*(k+1) when k+1 < |c|
      (if k+1 < |c| then c[k+1] * (k+1) as real else 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed array/seq assignment and used proper sequence initialization */
  result := [];
  var k := 0;
  while k < |c| + 1
    invariant k <= |c| + 1
    invariant |result| == k
    invariant forall i :: 0 <= i < k ==> result[i] == (if i > 0 && i-1 < |c| then c[i-1] / 2.0 else 0.0) + (if i+1 < |c| then c[i+1] * (i+1) as real else 0.0)
  {
    result := result + [(if k > 0 && k-1 < |c| then c[k-1] / 2.0 else 0.0) + (if k+1 < |c| then c[k+1] * (k+1) as real else 0.0)];
    k := k + 1;
  }
}
// </vc-code>
