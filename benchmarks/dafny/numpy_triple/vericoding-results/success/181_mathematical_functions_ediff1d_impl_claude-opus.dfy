// <vc-preamble>
// Method to compute differences between consecutive elements of an array
// </vc-preamble>

// <vc-helpers>

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
  result := [];
  var i := 0;
  while i < |ary| - 1
    invariant 0 <= i <= |ary| - 1
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == ary[j+1] - ary[j]
  {
    result := result + [ary[i+1] - ary[i]];
    i := i + 1;
  }
}
// </vc-code>
