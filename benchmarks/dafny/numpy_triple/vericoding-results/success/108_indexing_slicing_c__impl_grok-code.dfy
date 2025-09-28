// <vc-preamble>
// Method that creates a 2-D array by stacking two vectors as columns
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): No helpers needed */
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
  /* code modified by LLM (iteration 2): Fixed index out of range by using explicit loop with invariants */
  var n := |arr1|;
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> |result[j]| == 2 && result[j][0] == arr1[j] && result[j][1] == arr2[j]
  {
    result := result + [[arr1[i], arr2[i]]];
    i := i + 1;
  }
}
// </vc-code>
