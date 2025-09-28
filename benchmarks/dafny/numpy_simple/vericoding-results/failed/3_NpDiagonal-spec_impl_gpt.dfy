// <vc-preamble>
/* Matrix type represented as a sequence of sequences */
type Matrix<T> = seq<seq<T>>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): length of diagonal for given matrix size and offset k */
function diagLength(n: int, k: int): int
  requires 0 < n && -n < k < n
{
  if k > 0 then n - k else n + (-k)
}
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
  /* code modified by LLM (iteration 5): implement diagonal via correct Dafny sequence comprehension syntax */
  var n := |arr|;
  if k > 0 {
    result := seq i | 0 <= i < n - k :: arr[i][i + k];
  } else {
    result := seq i | 0 <= i < n + (-k) :: arr[i + (-k)][i];
  }
}
// </vc-code>
