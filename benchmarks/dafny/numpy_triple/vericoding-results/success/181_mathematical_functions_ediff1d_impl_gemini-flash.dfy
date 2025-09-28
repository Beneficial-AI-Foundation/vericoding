// <vc-preamble>
// Method to compute differences between consecutive elements of an array
// </vc-preamble>

// <vc-helpers>
// No helpers needed for straight-forward implementation
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
  var i := 0;
  var tempResult: seq<real> := [];

  while i < |ary| - 1
    invariant 0 <= i <= |ary| - 1
    invariant |tempResult| == i
    invariant forall k :: 0 <= k < i ==> tempResult[k] == ary[k+1] - ary[k]
  {
    tempResult := tempResult + [ary[i+1] - ary[i]];
    i := i + 1;
  }
  result := tempResult;
}
// </vc-code>
