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
lemma sum_abs_cons_step(arr: seq<int>, i: int)
    requires 0 <= i < |arr|
    ensures sum_abs(arr, i) == (if arr[i] >= 0 then arr[i] else -arr[i]) + sum_abs(arr, i + 1)
{
    // This lemma follows directly from the definition of sum_abs
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
        invariant result == sum_abs(arr, i)
    {
        var abs_val := if arr[i] >= 0 then arr[i] else -arr[i];
        result := result + abs_val;
        i := i + 1;
        
        // Prove the invariant is maintained
        assert sum_abs(arr, i - 1) == abs_val + sum_abs(arr, i) by {
            sum_abs_cons_step(arr, i - 1);
        }
        assert result == sum_abs(arr, i - 1) + abs_val;
        assert result == sum_abs(arr, i);
    }
}
// </vc-code>

