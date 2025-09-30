// <vc-preamble>
// Method that transforms a 1D vector into a 3D array with shape (1, n, 1)
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AtLeast3D(arr: seq<real>) returns (result: seq<seq<seq<real>>>)
    // Input can be any sequence of reals
    requires true
    // Output has shape (1, n, 1) where n is the length of input
    ensures |result| == 1
    ensures |result[0]| == |arr|
    ensures forall k :: 0 <= k < |result[0]| ==> |result[0][k]| == 1
    // Each element arr[i] is accessible at position [0][i][0] in the result
    ensures forall i :: 0 <= i < |arr| ==> result[0][i][0] == arr[i]
    // The result contains exactly the same elements as input, just reshaped
    ensures forall i :: 0 <= i < |arr| ==> 
        exists j, k, l :: 0 <= j < |result| && 
                         0 <= k < |result[j]| && 
                         0 <= l < |result[j][k]| && 
                         result[j][k][l] == arr[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added explicit assertions to help prove existential postcondition */
  var n := |arr|;
  var inner := seq(n, i requires 0 <= i < n => [arr[i]]);
  result := [inner];
  
  // Help Dafny prove the existential postcondition
  assert forall i :: 0 <= i < |arr| ==> 
    0 <= 0 < |result| && 
    0 <= i < |result[0]| && 
    0 <= 0 < |result[0][i]| && 
    result[0][i][0] == arr[i];
}
// </vc-code>
