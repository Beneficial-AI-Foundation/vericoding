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
lemma SumLowerBound(n: int, a1: seq<int>, a2: seq<int>, i: int)
    requires ValidInput(n, a1, a2)
    requires 0 <= i < n
    ensures sum_range(a1, 0, i+1) + sum_range(a2, i, n) >= n + 1
{
    assert sum_range(a1, 0, i+1) >= i+1;
    assert sum_range(a2, i, n) >= n - i;
}
 
lemma SumUpperBoundA1(n: int, a1: seq<int>, i: int)
    requires n >= 1 && |a1| == n && forall k :: 0 <= k < n ==> 1 <= a1[k] <= 100
    requires 0 <= i < n
    ensures sum_range(a1, 0, i+1) <= (i+1) * 100
{
    assert sum_range(a1, 0, i+1) <= (i+1) * 100;
}
 
lemma SumUpperBoundA2(n: int, a2: seq<int>, i: int)
    requires n >= 1 && |a2| == n && forall k :: 0 <= k < n ==> 1 <= a2[k] <= 100
    requires 0 <= i < n
    ensures sum_range(a2, i, n) <= (n - i) * 100
{
    assert sum_range(a2, i, n) <= (n - i) * 100;
}
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
    assert max_val >= n + 1;  // From ensures of sum_range, since min per element
    for i := 0 to n - 1 {
        var s1 := sum_range(a_1, 0, i + 1);
        var s2 := sum_range(a_2, i, n);
        assert s1 >= i + 1;  // From ensures of sum_range
        assert s2 >= n - i;  // From ensures of sum_range
        // So s1 + s2 >= (i + 1) + (n - i) = n + 1
        if s1 + s2 > max_val {
            max_val := s1 + s2;
            max_i := i;
        }
        // If not updated, max_val remains >= the previous max
    }
    // Call lemmas to establish upper bounds
    SumUpperBoundA1(n, a_1, max_i);
    SumUpperBoundA2(n, a_2, max_i);
    // Bound on max_val <= (n + 1) * 100
    assert sum_range(a_1, 0, max_i + 1) <= (max_i + 1) * 100;  // From ensures of sum_range, since ValidInput ensures values <= 100
    assert sum_range(a_2, max_i, n) <= (n - max_i) * 100;      // Similarly
    // Total (max_i + 1) * 100 + (n - max_i) * 100 = (n + 1) * 100 >= max_val
    assert max_val <= (n + 1) * 100;
    // Lower bound already established
    assert max_val >= n + 1;
    // The exists condition holds because max_i was set accordingly
    assert 0 <= max_i < n && max_val == sum_range(a_1, 0, max_i + 1) + sum_range(a_2, max_i, n);
    result := max_val;
}
// </vc-code>

