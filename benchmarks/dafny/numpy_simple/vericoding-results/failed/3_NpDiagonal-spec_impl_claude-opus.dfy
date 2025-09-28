// <vc-preamble>
/* Matrix type represented as a sequence of sequences */
type Matrix<T> = seq<seq<T>>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 5): Fixed result length calculation for negative k */
  result := [];
  var n := |arr|;
  
  if k > 0 {
    var i := 0;
    while i < n - k
      invariant 0 <= i <= n - k
      invariant |result| == i
      invariant forall j :: 0 <= j < i ==> result[j] == arr[j][j + k]
    {
      result := result + [arr[i][i + k]];
      i := i + 1;
    }
  } else {
    var offset := -k;
    var i := 0;
    while i < n + k
      invariant 0 <= i <= n + k
      invariant |result| == i
      invariant forall j :: 0 <= j < i ==> result[j] == arr[j + offset][j]
    {
      result := result + [arr[i + offset][i]];
      i := i + 1;
    }
  }
}
// </vc-code>
