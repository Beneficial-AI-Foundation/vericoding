// <vc-preamble>
// Find the intersection of two arrays, returning sorted unique values present in both
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method intersect1d(ar1: seq<int>, ar2: seq<int>) returns (result: seq<int>)
  ensures // Result contains only values that exist in both input arrays
    forall i :: 0 <= i < |result| ==> result[i] in ar1 && result[i] in ar2
  ensures // Result is sorted in strict ascending order (which ensures uniqueness)
    forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
  ensures // Result is complete - contains all values that appear in both arrays
    forall val :: val in ar1 && val in ar2 ==> val in result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Updated loop invariants to correctly ensure all common elements are included and maintain sorted order */
  var ar2_set := set x | x in ar2 :: x;
  var result_temp: seq<int> := [];
  var i := 0;
  while i < |ar1|
    invariant 0 <= i <= |ar1|
    invariant forall k :: 0 <= k < |result_temp| ==> result_temp[k] in ar1[0..i] && result_temp[k] in ar2_set
    invariant forall k, m :: 0 <= k < m < |result_temp| ==> result_temp[k] < result_temp[m]
    invariant forall val :: val in ar1[0..i] && val in ar2_set ==> val in result_temp
  {
    if ar1[i] in ar2_set {
      var pos := 0;
      while pos < |result_temp| && result_temp[pos] < ar1[i]
        invariant 0 <= pos <= |result_temp|
        invariant forall p :: 0 <= p < pos ==> result_temp[p] < ar1[i]
      {
        pos := pos + 1;
      }
      if !(exists p :: 0 <= p < |result_temp| && result_temp[p] == ar1[i]) {
        result_temp := result_temp[..pos] + [ar1[i]] + result_temp[pos..];
      }
    }
    i := i + 1;
  }
  result := result_temp;
}
// </vc-code>
