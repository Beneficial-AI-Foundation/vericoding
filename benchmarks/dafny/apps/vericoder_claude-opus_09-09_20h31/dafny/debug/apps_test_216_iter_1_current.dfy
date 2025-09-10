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
lemma sum_abs_append(arr: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |arr|
    ensures sum_abs(arr, i) == sum_abs(arr[..j], i) + sum_abs(arr, j)
    decreases j - i
{
    if i == j {
        assert arr[..j] == arr[..i];
    } else {
        sum_abs_append(arr, i + 1, j);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, arr: seq<int>) returns (result: int)
    requires ValidInput(n, arr)
    ensures result == sum_abs(arr, 0)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    result := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant n == |arr|
        invariant result == sum_abs(arr[..i], 0)
    {
        var abs_val := if arr[i] >= 0 then arr[i] else -arr[i];
        
        assert arr[..i+1] == arr[..i] + [arr[i]];
        assert sum_abs(arr[..i+1], 0) == sum_abs(arr[..i], 0) + abs_val;
        
        result := result + abs_val;
        i := i + 1;
    }
    
    assert i == n;
    assert arr[..n] == arr;
    assert result == sum_abs(arr[..n], 0) == sum_abs(arr, 0);
}
// </vc-code>

