// <vc-preamble>
function sum_abs(arr: seq<int>, i: int): int
    requires 0 <= i <= |arr|
    decreases |arr| - i
{
    if i == |arr| then 0
    else (if arr[i] >= 0 then arr[i] else -arr[i]) + sum_abs(arr, i + 1)
}

predicate ValidInput(n: int, arr: seq<int>)
{
    0 <= n == |arr|
}
// </vc-preamble>

// <vc-helpers>
function abs(x: int): int {
    if x < 0 then -x else x
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, arr: seq<int>) returns (result: int)
    requires ValidInput(n, arr)
    ensures result == sum_abs(arr, 0)
// </vc-spec>
// <vc-code>
{
    var total_sum := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant total_sum == sum_abs(arr, 0) - sum_abs(arr, i)
    {
        total_sum := total_sum + abs(arr[i]);
        i := i + 1;
    }
    result := total_sum;
}
// </vc-code>
