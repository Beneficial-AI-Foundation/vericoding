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
lemma LemmaPrefixSumCorrectness(n: int, a: seq<int>, prefix: array<int>)
    requires n == |a| == prefix.Length
    requires forall i :: 0 <= i < n ==> prefix[i] == (if i == 0 then a[0] else prefix[i-1] + a[i])
    ensures forall i :: 0 <= i < n ==> prefix[i] == sum_range(a, 0, i+1)
{
    if n == 0 {
    } else {
        calc {
            prefix[0];
            { assert prefix[0] == a[0]; }
            a[0];
            sum_range(a, 0, 1);
        }
        var i := 1;
        while i < n
            invariant 1 <= i <= n
            invariant forall k :: 0 <= k < i ==> prefix[k] == sum_range(a, 0, k+1)
        {
            calc {
                prefix[i];
                prefix[i-1] + a[i];
                { assert prefix[i-1] == sum_range(a, 0, i); }
                sum_range(a, 0, i) + a[i];
                sum_range(a, 0, i+1);
            }
            i := i + 1;
        }
    }
}

lemma LemmaSuffixSumCorrectness(n: int, a: seq<int>, suffix: array<int>)
    requires n == |a| == suffix.Length
    requires forall i :: 0 <= i < n ==> suffix[i] == (if i == n-1 then a[n-1] else a[i] + suffix[i+1])
    ensures forall i :: 0 <= i < n ==> suffix[i] == sum_range(a, i, n)
{
    if n == 0 {
    } else {
        calc {
            suffix[n-1];
            a[n-1];
            sum_range(a, n-1, n);
        }
        var i := n-2;
        while i >= 0
            invariant -1 <= i < n-1
            invariant forall k :: i < k < n ==> suffix[k] == sum_range(a, k, n)
        {
            calc {
                suffix[i];
                a[i] + suffix[i+1];
                { assert suffix[i+1] == sum_range(a, i+1, n); }
                a[i] + sum_range(a, i+1, n);
                sum_range(a, i, n);
            }
            i := i - 1;
        }
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
    var prefix: array<int> := new int[n];
    var suffix: array<int> := new int[n];
    
    // Compute prefix sums for a_1
    if n >= 1 {
        prefix[0] := a_1[0];
    }
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant forall k :: 0 <= k < i ==> prefix[k] == (if k == 0 then a_1[0] else prefix[k-1] + a_1[k])
    {
        prefix[i] := prefix[i-1] + a_1[i];
        i := i + 1;
    }
    LemmaPrefixSumCorrectness(n, a_1, prefix);
    
    // Compute suffix sums for a_2
    if n >= 1 {
        suffix[n-1] := a_2[n-1];
    }
    i := n - 2;
    while i >= 0
        invariant -1 <= i < n-1
        invariant forall k :: i < k < n ==> suffix[k] == (if k == n-1 then a_2[n-1] else a_2[k] + suffix[k+1])
    {
        suffix[i] := a_2[i] + suffix[i+1];
        i := i - 1;
    }
    LemmaSuffixSumCorrectness(n, a_2, suffix);
    
    // Find maximum candidate value
    result := prefix[0] + suffix[0];
    i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant forall k :: 0 <= k < i ==> result >= prefix[k] + suffix[k]
        invariant exists k :: 0 <= k < i && result == prefix[k] + suffix[k]
        invariant n+1 <= result <= (n+1)*100
    {
        var candidate := prefix[i] + suffix[i];
        if candidate > result {
            result := candidate;
        }
        i := i + 1;
    }
}
// </vc-code>

