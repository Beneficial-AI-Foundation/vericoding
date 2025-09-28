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
  /* code modified by LLM (iteration 5): [Fixed compilation error by changing `seq_init` to the correct Dafny sequence constructor `seq`.] */
  var n := |arr|;
  if k > 0 {
    result := seq(n - k, (i: nat) => arr[i][i + k]);
  } else { // k <= 0
    var m := -k;
    result := seq(n + m, (i: nat) => arr[i + m][i]);
  }
}
// </vc-code>
