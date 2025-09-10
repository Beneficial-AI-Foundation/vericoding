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

// <vc-helpers>
// <vc-helpers>
// Add lemma to help prove sum >= n+1
lemma SumLowerBound(n: int, a1: seq<int>, a2: seq<int>, i: int)
    requires ValidInput(n, a1, a2)
    requires 0 <= i < n
    ensures sum_range(a1, 0, i+1) + sum_range(a2, i, n) >= n + 1
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, a_1: seq<int>, a_2: seq<int>) returns (result: int)
    requires ValidInput(n, a_1, a_2)
    ensures IsValidResult(n, a_1, a_2, result)
// </vc-spec>
// <vc-code>
{
    var max_val := sum_range(a_1, 0, 1) + sum_range(a_2, 0, n);
    var max_i := 0;
    for i := 0 to n - 1 {
        var s1 := sum_range(a_1, 0, i + 1);
        var s2 := sum_range(a_2, i, n);
        if s1 + s2 > max_val {
            max_val := s1 + s2;
            max_i := i;
        }
    }

    // Assert bounds
    assert max_val >= n + 1;  // From lemma or direct
    assert max_val <= (n + 1) * 100;

    // Assert the exists condition
    assert 0 <= max_i < n && max_val == sum_range(a_1, 0, max_i + 1) + sum_range(a_2, max_i, n);

    result := max_val;
}
// </vc-code>

