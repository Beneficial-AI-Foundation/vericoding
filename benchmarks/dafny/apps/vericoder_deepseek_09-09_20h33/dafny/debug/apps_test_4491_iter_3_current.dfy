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
lemma lemma_sum_range_properties(s: seq<int>, start: int, end: int, i: int)
    requires 0 <= start <= end <= |s|
    requires forall j :: start <= j < end ==> s[j] >= 1
    requires start <= i < end
    ensures sum_range(s, start, end) >= s[i]
    decreases end - start
{
    if start < end {
        if start == i {
            // Directly from the definition
        } else {
            lemma_sum_range_properties(s, start + 1, end, i);
        }
    }
}

lemma lemma_sum_range_split(s: seq<int>, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= |s|
    requires forall j :: start <= j < end ==> s[j] >= 1
    ensures sum_range(s, start, end) == sum_range(s, start, mid) + sum_range(s, mid, end)
    decreases end - start
{
    if start < mid {
        lemma_sum_range_split(s, start + 1, mid, end);
    }
}

lemma lemma_sum_range_monotonic(s: seq<int>, start: int, end: int, k: int)
    requires 0 <= start <= k <= end <= |s|
    requires forall j :: start <= j < end ==> s[j] >= 1
    ensures sum_range(s, start, end) >= sum_range(s, start, k)
    decreases end - k
{
    if k < end {
        var rest := sum_range(s, k, end);
        assert rest >= 0;
        lemma_sum_range_monotonic(s, start, end, k + 1);
    }
}

lemma lemma_sum_exists(n: int, a_1: seq<int>, a_2: seq<int>)
    requires ValidInput(n, a_1, a_2)
    ensures exists i :: 0 <= i < n && sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) >= n + 1 && sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) <= (n + 1) * 100
{
    var i := 0;
    var total := sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n);
    assert total >= n + 1 && total <= (n + 1) * 100;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a_1: seq<int>, a_2: seq<int>) returns (result: int)
    requires ValidInput(n, a_1, a_2)
    ensures IsValidResult(n, a_1, a_2, result)
// </vc-spec>
// <vc-code>
{
    var min_total := (n + 1) * 100 + 1;
    var best_i := 0;
    var index := 0;
    
    while index < n
        invariant 0 <= index <= n
        invariant best_i < n || index == 0
        invariant exists i :: 0 <= i < index && min_total == sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)
        invariant forall i :: 0 <= i < index ==> min_total <= sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)
        invariant min_total >= n + 1 && min_total <= (n + 1) * 100
    {
        var total := sum_range(a_1, 0, index + 1) + sum_range(a_2, index, n);
        if total < min_total {
            min_total := total;
            best_i := index;
        }
        index := index + 1;
    }
    
    result := min_total;
}
// </vc-code>

