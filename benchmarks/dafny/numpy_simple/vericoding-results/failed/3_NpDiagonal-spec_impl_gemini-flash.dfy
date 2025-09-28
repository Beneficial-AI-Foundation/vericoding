// <vc-preamble>
/* Matrix type represented as a sequence of sequences */
type Matrix<T> = seq<seq<T>>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed reads clause from predicate, as it is not needed */
predicate IsSquareMatrix<T>(matrix: Matrix<T>)
{
    |matrix| > 0 &&
    (forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix|)
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
/* code modified by LLM (iteration 5): fixed index out of range issues in seq initialisation */
{
    var size := |arr|;
    if k > 0 {
        result := seq(size - k, i => arr[i][i + k]);
    } else {
        result := seq(size - k, i => arr[i - k][i]);
    }
}
// </vc-code>
