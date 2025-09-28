// <vc-preamble>
/* Matrix type represented as a sequence of sequences */
type Matrix<T> = seq<seq<T>>
// </vc-preamble>

// <vc-helpers>
function abs(x: int): int { if x >= 0 then x else -x }

function getDiagonalLength(n: int, k: int): int {
  if k >= 0 then n - k else n + k
}

lemma diagonalBounds(i: int, n: int, k: int)
  requires 0 <= i < getDiagonalLength(n, k)
  requires -n < k < n
  ensures if k >= 0 then
    0 <= i < n && 0 <= i + k < n
  else
    0 <= i - k < n && 0 <= i < n
{
}

/* helper modified by LLM (iteration 5): Fixed ensures condition to use i - k instead of i + (-k) for consistency */
lemma diagonalAccessValid(arr: Matrix<int>, i: int, k: int)
  requires |arr| > 0 && |arr| == |arr[0]| && (forall i :: 0 <= i < |arr| ==> |arr[i]| == |arr|)
  requires -|arr| < k < |arr|
  requires 0 <= i < getDiagonalLength(|arr|, k)
  ensures if k >= 0 then
    arr[i][i + k] == arr[i][i + k]
  else
    arr[i - k][i] == arr[i - k][i]
{
  diagonalBounds(i, |arr|, k);
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
  /* code modified by LLM (iteration 5): Fixed array access to use i - k instead of i + (-k) for better verification */
  var n := |arr|;
  var len := getDiagonalLength(n, k);
  result := [];
  
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> 
      if k >= 0 then
        0 <= j < n && 0 <= j + k < n && result[j] == arr[j][j + k]
      else
        0 <= j - k < n && 0 <= j < n && result[j] == arr[j - k][j]
  {
    diagonalBounds(i, n, k);
    if k >= 0 {
      result := result + [arr[i][i + k]];
    } else {
      result := result + [arr[i - k][i]];
    }
    i := i + 1;
  }
}
// </vc-code>
