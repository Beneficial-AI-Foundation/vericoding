// <vc-preamble>
// Helper function to compute the factorial-like factor for polynomial differentiation
// Computes original_idx * (original_idx - 1) * ... * (original_idx - m + 1)
function factorial_factor(original_idx: nat, m: nat): real
  decreases m
{
  if m == 0 then 1.0
  else (original_idx - (m - 1)) as real * factorial_factor(original_idx, m - 1)
}

// Helper function to compute scaling factor scl^m
function scale_factor(scl: real, m: nat): real
  decreases m
{
  if m == 0 then 1.0
  else scl * scale_factor(scl, m - 1)
}

// Polynomial differentiation method
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method polyder(c: seq<real>, m: nat, scl: real) returns (result: seq<real>)
  requires m <= |c|
  ensures |result| == |c| - m
  ensures m == 0 ==> result == c
  ensures m > 0 ==> forall i :: 0 <= i < |result| ==> 
    result[i] == c[i + m] * factorial_factor(i + m, m) * scale_factor(scl, m)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Replaced seq comprehension with a while loop to resolve index out of range error. */
  if m == 0 {
    result := c;
  } else {
    var temp_result: seq<real> := [];
    var i := 0;
    while i < |c| - m
      invariant |temp_result| == i
      invariant 0 <= i <= |c| - m
      invariant forall k :: 0 <= k < i ==> temp_result[k] == c[k + m] * factorial_factor(k + m, m) * scale_factor(scl, m)
    {
      // The loop invariant i < |c| - m proves that i + m < |c|
      var new_val := c[i + m] * factorial_factor(i + m, m) * scale_factor(scl, m);
      temp_result := temp_result + [new_val];
      i := i + 1;
    }
    result := temp_result;
  }
}
// </vc-code>
