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
lemma sum_range_single(s: seq<int>, i: int)
    requires 0 <= i < |s|
    requires s[i] >= 1
    ensures sum_range(s, i, i + 1) == s[i]
{
}

lemma sum_range_split(s: seq<int>, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= |s|
    requires forall i :: start <= i < end ==> s[i] >= 1
    ensures sum_range(s, start, end) == sum_range(s, start, mid) + sum_range(s, mid, end)
    decreases end - start
{
    if start == mid {
    } else {
        sum_range_split(s, start + 1, mid, end);
    }
}

lemma sum_range_append(s: seq<int>, start: int, end: int)
    requires 0 <= start <= end < |s|
    requires forall i :: start <= i <= end ==> s[i] >= 1
    ensures sum_range(s, start, end + 1) == sum_range(s, start, end) + s[end]
    decreases end - start
{
    if start == end {
        sum_range_single(s, end);
    } else {
        sum_range_append(s, start + 1, end);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a_1: seq<int>, a_2: seq<int>) returns (result: int)
    requires ValidInput(n, a_1, a_2)
    ensures IsValidResult(n, a_1, a_2, result)
// </vc-spec>
// <vc-code>
{
    var min_sum := sum_range(a_1, 0, 1) + sum_range(a_2, 0, n);
    var min_index := 0;
    var i := 1;
    
    while i < n
        invariant 1 <= i <= n
        invariant min_sum >= n + 1
        invariant min_sum <= (n + 1) * 100
        invariant 0 <= min_index < i
        invariant min_sum == sum_range(a_1, 0, min_index + 1) + sum_range(a_2, min_index, n)
        invariant forall j :: 0 <= j < i ==> min_sum <= sum_range(a_1, 0, j + 1) + sum_range(a_2, j, n)
    {
        var current_sum := sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n);
        
        if current_sum < min_sum {
            min_sum := current_sum;
            min_index := i;
        }
        
        i := i + 1;
    }
    
    assert min_index < n;
    assert min_sum == sum_range(a_1, 0, min_index + 1) + sum_range(a_2, min_index, n);
    assert forall j :: 0 <= j < n ==> min_sum <= sum_range(a_1, 0, j + 1) + sum_range(a_2, j, n);
    
    result := min_sum;
}
// </vc-code>

