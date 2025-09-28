// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 2): fixed compilation warning by adding parentheses to the loop invariant */
  var n := |c|;
  var res_array := new real[n + 1];

  var k := 0;
  while k < n + 1
    invariant 0 <= k <= n + 1
    invariant forall j :: 0 <= j < k ==> (res_array[j] == 
      (if j > 0 && j-1 < |c| then c[j-1] / 2.0 else 0.0) +
      (if j+1 < |c| then c[j+1] * (j+1) as real else 0.0))
  {
    var term1: real := if k > 0 then c[k-1] / 2.0 else 0.0;
    var term2: real := if k+1 < |c| then c[k+1] * (k+1) as real else 0.0;
    res_array[k] := term1 + term2;
    k := k + 1;
  }

  result := res_array[..];
}
// </vc-code>
