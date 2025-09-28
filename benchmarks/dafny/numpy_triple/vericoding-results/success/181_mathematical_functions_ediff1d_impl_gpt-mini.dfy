// <vc-preamble>
// Method to compute differences between consecutive elements of an array
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): helper to check valid index within sequence */
function validIndex<T>(s: seq<T>, i: int): bool { 0 <= i < |s| }
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
  /* code modified by LLM (iteration 3): compute consecutive differences using array and loop */
  var n := |ary|;
  var m := n - 1;
  var a := new real[m];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant forall j :: 0 <= j < i ==> a[j] == ary[j+1] - ary[j]
  {
    a[i] := ary[i+1] - ary[i];
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
