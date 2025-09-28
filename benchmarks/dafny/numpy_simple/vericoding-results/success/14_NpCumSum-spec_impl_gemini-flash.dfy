// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Simplified the base case of `SumRange` and added a more appropriate `decreases` clause. */
function SumRange(arr: array<int>, start: int, end: int): int
    reads arr
    requires 0 <= start <= end < arr.Length
    decreases end - start
{
    if start == end then arr[end] // Changed from arr[start] to arr[end] for clarity when start == end
    else arr[start] + SumRange(arr, start + 1, end)
}
// </vc-helpers>

// <vc-spec>
method CumSum(a: array<int>) returns (result: array<int>)
    requires a.Length > 0
    ensures 
        result.Length == a.Length &&
        result[0] == a[0] &&
        forall i :: 1 <= i < a.Length ==> result[i] == result[i - 1] + a[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Changed loop invariant to ensure `result[k]` is correctly computed for all `k` up to `i-1` for `SumRange` and that the first element of `result` matches `a[0]`. The `SumRange` function is more appropriate for verifying the final state rather than in the loop as an invariant. */
{
    result := new int[a.Length];
    result[0] := a[0];
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall k :: 1 <= k < i ==> result[k] == result[k - 1] + a[k]
        invariant result[0] == a[0]
    {
        result[i] := result[i - 1] + a[i];
        i := i + 1;
    }
}
// </vc-code>
