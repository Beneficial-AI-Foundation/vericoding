// <vc-preamble>
// Method to compute differences between consecutive elements of an array
// </vc-preamble>

// <vc-helpers>
function diffAt(ary: seq<real>, i: int): real
  requires 0 <= i < |ary| - 1
{
  ary[i+1] - ary[i]
}
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
  var n := |ary|;
  var res: seq<real> := [];
  var i := 0;
  while i < n - 1
    invariant n == |ary|
    invariant 0 <= i && i <= n - 1
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == ary[j+1] - ary[j]
  {
    res := res + [diffAt(ary, i)];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
