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

// <vc-helpers>
lemma sum_abs_loop_invariant(arr: seq<int>, i: int, acc: int)
    requires 0 <= i <= |arr|
    requires acc == sum_abs(arr, 0) - sum_abs(arr, i)
    ensures acc + sum_abs(arr, i) == sum_abs(arr, 0)
{
}

lemma sum_abs_step(arr: seq<int>, i: int)
    requires 0 <= i < |arr|
    ensures sum_abs(arr, i) == (if arr[i] >= 0 then arr[i] else -arr[i]) + sum_abs(arr, i + 1)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, arr: seq<int>) returns (result: int)
    requires ValidInput(n, arr)
    ensures result == sum_abs(arr, 0)
// </vc-spec>
// <vc-code>
{
    result := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant result == sum_abs(arr, 0) - sum_abs(arr, i)
        decreases n - i
    {
        if arr[i] >= 0 {
            result := result + arr[i];
        } else {
            result := result - arr[i];
        }
        i := i + 1;
    }
}
// </vc-code>

