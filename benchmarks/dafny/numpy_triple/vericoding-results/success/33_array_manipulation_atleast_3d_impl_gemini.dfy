// <vc-preamble>
// Method that transforms a 1D vector into a 3D array with shape (1, n, 1)
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Changed to a recursive implementation to resolve a compilation error with seq initializers. */
function CreateMiddleLayer(arr: seq<real>): (res: seq<seq<real>>)
  ensures |res| == |arr|
  ensures forall k :: 0 <= k < |arr| ==> |res[k]| == 1 && res[k][0] == arr[k]
  decreases |arr|
{
  if |arr| == 0 then
    []
  else
    CreateMiddleLayer(arr[..|arr|-1]) + [[arr[|arr|-1]]]
}
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
  /* code modified by LLM (iteration 2): No change to logic, but verification should now pass with the fixed helper function. */
  result := [CreateMiddleLayer(arr)];
}
// </vc-code>
