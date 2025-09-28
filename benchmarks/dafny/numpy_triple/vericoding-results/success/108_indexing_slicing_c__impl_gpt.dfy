// <vc-preamble>
// Method that creates a 2-D array by stacking two vectors as columns
// </vc-preamble>

// <vc-helpers>
function Row(a: real, b: real): seq<real>
  ensures |Row(a, b)| == 2
  ensures Row(a, b)[0] == a && Row(a, b)[1] == b
{
  [a, b]
}
// </vc-helpers>

// <vc-spec>
method c_(arr1: seq<real>, arr2: seq<real>) returns (result: seq<seq<real>>)
  // Precondition: input arrays must have the same length
  requires |arr1| == |arr2|
  
  // Postconditions: result structure and content
  ensures |result| == |arr1|  // result has same number of rows as input length
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == 2  // each row has exactly 2 columns
  ensures forall i :: 0 <= i < |result| ==> 
    result[i][0] == arr1[i] && result[i][1] == arr2[i]  // correct column placement
// </vc-spec>
// <vc-code>
{
  var n := |arr1|;
  var res: seq<seq<real>> := [];
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall j :: 0 <= j < |res| ==> |res[j]| == 2 && res[j][0] == arr1[j] && res[j][1] == arr2[j]
  {
    assert i < |arr2|;
    var row := Row(arr1[i], arr2[i]);
    res := res + [row];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
