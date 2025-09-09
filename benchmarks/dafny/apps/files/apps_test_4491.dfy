Given a 2×N grid where each cell contains candies, find the maximum number of candies
that can be collected when traveling from top-left to bottom-right. You can only move
right or down, and you collect all candies from visited cells.

predicate ValidInput(n: int, a_1: seq<int>, a_2: seq<int>)
{
    n >= 1 &&
    |a_1| == n && |a_2| == n &&
    forall i :: 0 <= i < n ==> 1 <= a_1[i] <= 100 && 1 <= a_2[i] <= 100
}

function sum_range(s: seq<int>, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    requires forall i :: start <= i < end ==> s[i] >= 1
    decreases end - start
    ensures sum_range(s, start, end) >= 0
    ensures start < end ==> sum_range(s, start, end) >= end - start
    ensures start < end && (forall i :: start <= i < end ==> s[i] <= 100) ==> sum_range(s, start, end) <= (end - start) * 100
{
    if start == end then 0
    else s[start] + sum_range(s, start + 1, end)
}

predicate IsValidResult(n: int, a_1: seq<int>, a_2: seq<int>, result: int)
    requires ValidInput(n, a_1, a_2)
{
    result >= n + 1 &&
    result <= (n + 1) * 100 &&
    exists i :: 0 <= i < n && result == sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) &&
    forall i :: 0 <= i < n ==> result >= sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)
}

method solve(n: int, a_1: seq<int>, a_2: seq<int>) returns (result: int)
    requires ValidInput(n, a_1, a_2)
    ensures IsValidResult(n, a_1, a_2, result)
{
    var tmpCall1 := sum_range(a_1, 0, 1);
    var sum1 := tmpCall1;
    var sum2 := sum_range(a_2, 0, n);
    var ans := sum1 + sum2;

    // Prove initial bounds
    assert sum1 == a_1[0];
    assert sum1 >= 1 && sum1 <= 100;
    assert sum2 >= n && sum2 <= n * 100;
    assert ans >= n + 1;
    assert ans <= (n + 1) * 100;

    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant ans >= n + 1
        invariant exists j :: 0 <= j < i && ans == sum_range(a_1, 0, j + 1) + sum_range(a_2, j, n)
        invariant forall j :: 0 <= j < i ==> ans >= sum_range(a_1, 0, j + 1) + sum_range(a_2, j, n)
        invariant ans <= (n + 1) * 100
    {
        var tmpCall2 := sum_range(a_1, 0, i + 1);
        var sum1_new := tmpCall2;
        var sum2_new := sum_range(a_2, i, n);
        var total := sum1_new + sum2_new;

        // Prove bounds for the new total
        assert sum1_new >= i + 1 && sum1_new <= (i + 1) * 100;
        assert sum2_new >= n - i && sum2_new <= (n - i) * 100;
        assert total >= n + 1;
        assert total <= (n + 1) * 100;

        if total > ans {
            ans := total;
        }
        i := i + 1;
    }
    result := ans;
}
