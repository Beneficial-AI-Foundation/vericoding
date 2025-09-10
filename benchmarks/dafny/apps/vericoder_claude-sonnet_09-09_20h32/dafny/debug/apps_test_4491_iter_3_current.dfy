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
lemma SumRangeProperties(s: seq<int>, start: int, end: int)
    requires 0 <= start <= end <= |s|
    requires forall i :: start <= i < end ==> 1 <= s[i] <= 100
    ensures sum_range(s, start, end) >= 0
    ensures start < end ==> sum_range(s, start, end) >= end - start
    ensures start < end ==> sum_range(s, start, end) <= (end - start) * 100
{
}

lemma SumRangeMonotonic(s: seq<int>, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= |s|
    requires forall i :: start <= i < end ==> 1 <= s[i] <= 100
    ensures sum_range(s, start, mid) <= sum_range(s, start, end)
    decreases end - mid
{
    if mid < end {
        assert s[mid] >= 1;
        assert sum_range(s, start, end) == sum_range(s, start, mid) + sum_range(s, mid, end);
        assert sum_range(s, mid, end) >= 0;
        SumRangeMonotonic(s, start, mid + 1, end);
    }
}

lemma ValidResultExists(n: int, a_1: seq<int>, a_2: seq<int>)
    requires ValidInput(n, a_1, a_2)
    ensures exists min_val :: {:trigger IsValidResult(n, a_1, a_2, min_val)} (min_val >= n + 1 && min_val <= (n + 1) * 100 &&
            (exists i :: 0 <= i < n && min_val == sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)) &&
            (forall i :: 0 <= i < n ==> min_val <= sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)))
{
    var vals := seq(n, i requires 0 <= i < n => sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n));
    
    forall i | 0 <= i < n
        ensures vals[i] >= n + 1
        ensures vals[i] <= (n + 1) * 100
    {
        SumRangeProperties(a_1, 0, i + 1);
        SumRangeProperties(a_2, i, n);
    }
    
    var min_val := vals[0];
    var min_idx := 0;
    
    var j := 1;
    while j < n
        invariant 1 <= j <= n
        invariant 0 <= min_idx < j
        invariant min_val == vals[min_idx]
        invariant forall k :: 0 <= k < j ==> min_val <= vals[k]
    {
        if vals[j] < min_val {
            min_val := vals[j];
            min_idx := j;
        }
        j := j + 1;
    }
    
    assert forall k :: 0 <= k < n ==> min_val <= vals[k];
    assert min_val == vals[min_idx];
    assert min_val == sum_range(a_1, 0, min_idx + 1) + sum_range(a_2, min_idx, n);
}

lemma FindMinimumCorrect(n: int, a_1: seq<int>, a_2: seq<int>, min_val: int, min_idx: int)
    requires ValidInput(n, a_1, a_2)
    requires 0 <= min_idx < n
    requires min_val == sum_range(a_1, 0, min_idx + 1) + sum_range(a_2, min_idx, n)
    requires forall i :: 0 <= i < n ==> min_val <= sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)
    ensures IsValidResult(n, a_1, a_2, min_val)
{
    SumRangeProperties(a_1, 0, min_idx + 1);
    SumRangeProperties(a_2, min_idx, n);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a_1: seq<int>, a_2: seq<int>) returns (result: int)
    requires ValidInput(n, a_1, a_2)
    ensures IsValidResult(n, a_1, a_2, result)
// </vc-spec>
// <vc-code>
{
    var min_val := sum_range(a_1, 0, 1) + sum_range(a_2, 0, n);
    var min_idx := 0;
    
    var i := 1;
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= min_idx < i
        invariant min_val == sum_range(a_1, 0, min_idx + 1) + sum_range(a_2, min_idx, n)
        invariant forall j :: 0 <= j < i ==> min_val <= sum_range(a_1, 0, j + 1) + sum_range(a_2, j, n)
    {
        var current_val := sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n);
        if current_val < min_val {
            min_val := current_val;
            min_idx := i;
        }
        i := i + 1;
    }
    
    assert forall j :: 0 <= j < n ==> min_val <= sum_range(a_1, 0, j + 1) + sum_range(a_2, j, n);
    assert min_val == sum_range(a_1, 0, min_idx + 1) + sum_range(a_2, min_idx, n);
    assert 0 <= min_idx < n;
    
    FindMinimumCorrect(n, a_1, a_2, min_val, min_idx);
    result := min_val;
}
// </vc-code>

