// <vc-preamble>
/* Matrix type represented as a sequence of sequences */
type Matrix<T> = seq<seq<T>>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
method diagonal(arr: Matrix<int>, k: int) returns (result: seq<int>)
    requires 
        |arr| > 0 &&
        |arr| == |arr[0]| && /* square matrix */
        (forall i :: 0 <= i < |arr| ==> |arr[i]| == |arr|) &&
        -|arr| < k < |arr|
    ensures
        if k > 0 then
            |result| == |arr| - k &&
            forall i :: 0 <= i < |result| ==> 
                0 <= i < |arr| && 0 <= i + k < |arr| && result[i] == arr[i][i + k]
        else
            |result| == |arr| + (-k) &&
            forall i :: 0 <= i < |result| ==> 
                0 <= i + (-k) < |arr| && 0 <= i < |arr| && result[i] == arr[i + (-k)][i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): unified loop bounds for both cases and added necessary invariants */
  var n := |arr|;
  result := [];
  if k > 0 {
    for i := 0 to n - k - 1
      invariant |result| == i
      invariant forall j :: 0 <= j < i ==> 0 <= j < n && 0 <= j + k < n && result[j] == arr[j][j + k]
    {
      result := result + [arr[i][i + k]];
    }
  } else {
    for i := 0 to n - k - 1
      invariant |result| == i
      invariant forall j :: 0 <= j < i ==> 0 <= j < n && 0 <= j + (-k) < n && result[j] == arr[j + (-k)][j]
    {
      result := result + [arr[i - k][i]];
    }
  }
}
// </vc-code>
