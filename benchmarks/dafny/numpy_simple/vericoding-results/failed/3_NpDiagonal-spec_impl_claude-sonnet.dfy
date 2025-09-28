// <vc-preamble>
/* Matrix type represented as a sequence of sequences */
type Matrix<T> = seq<seq<T>>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma to properly establish bounds */
lemma lowerDiagonalBounds(n: int, k: int, i: int)
    requires n > 0 && k <= 0 && -n < k < n
    requires 0 <= i < n + (-k)
    ensures 0 <= i + (-k) < n && 0 <= i < n
{
    assert 0 <= i;
    assert i < n + (-k);
    assert -k > 0;
    assert i + (-k) >= 0 + (-k) == -k > -n;
    assert i + (-k) < (n + (-k)) + (-k) == n - 2*(-k);
    assert -k < n;
    assert i + (-k) < n + (-k) - k == n - 2*k;
    assert k <= 0 ==> -k >= 0;
    assert i + (-k) >= -k >= 0;
    assert i + (-k) < n;
}

lemma upperDiagonalBounds(n: int, k: int, i: int)
    requires n > 0 && k > 0 && -n < k < n
    requires 0 <= i < n - k
    ensures 0 <= i < n && 0 <= i + k < n
{
    assert 0 <= i;
    assert i < n - k < n;
    assert i + k < (n - k) + k == n;
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
    /* code modified by LLM (iteration 5): fix matrix access with correct bounds */
    var n := |arr|;
    if k > 0 {
        result := seq(n - k, i requires 0 <= i < n - k => arr[i][i + k]);
    } else {
        result := seq(n + (-k), i requires 0 <= i < n + (-k) => arr[i + (-k)][i]);
    }
}
// </vc-code>
