// <vc-preamble>
// Method to compute differences between consecutive elements of an array
// </vc-preamble>

// <vc-helpers>
function diff(a: real, b: real): real { b - a }
/* helper modified by LLM (iteration 3): maintained correct difference helper */
// </vc-helpers>

// <vc-spec>
method numpy_ediff1d(ary: seq<real>) returns (result: seq<real>)
  // Input array must have at least one element
  requires |ary| >= 1
  // Result has length n for input of length n+1
  ensures |result| == |ary| - 1
  // Each element represents difference between consecutive elements: result[i] = ary[i+1] - ary[i]
  ensures forall i :: 0 <= i < |result| ==> result[i] == ary[i+1] - ary[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed index access in loop invariant */
  result := [];
  var j := 0;
  while j < |ary| - 1
    invariant 0 <= j <= |ary| - 1
    invariant |result| == j
    invariant forall k :: 0 <= k < j ==> result[k] == ary[k+1] - ary[k]
  {
    var d := diff(ary[j], ary[j+1]);
    result := result + [d];
    j := j + 1;
  }
}
// </vc-code>
