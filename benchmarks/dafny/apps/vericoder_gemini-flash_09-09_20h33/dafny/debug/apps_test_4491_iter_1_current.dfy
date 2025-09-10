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
function calculate_sum(a_1: seq<int>, a_2: seq<int>, n: int, i: int): int
    requires 0 <= i < n
    requires forall j :: 0 <= j < n ==> 1 <= a_1[j] <= 100
    requires forall j :: 0 <= j < n ==> 1 <= a_2[j] <= 100
    ensures calculate_sum(a_1, a_2, n, i) == sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)
    ensures 1 <= a_1[0] && 1 <= a_2[n-1] ==> calculate_sum(a_1, a_2, n, i) >= n + 1
{
    sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a_1: seq<int>, a_2: seq<int>) returns (result: int)
    requires ValidInput(n, a_1, a_2)
    ensures IsValidResult(n, a_1, a_2, result)
// </vc-spec>
// <vc-code>
{
    var min_sum := (n + 1) * 100; // Initialize with a value larger than any possible sum
    var found_an_index := false;

    // Proofs for min_sum bounds
    // (n+1) is the minimum length for the combined path (i+1) + (n-i)
    // Each element is at least 1, so the minimum sum is (n+1)*1
    // Each element is at most 100, so the maximum sum is (n+1)*100
    // We expect the min_sum to be >= n+1
    // We expect the min_sum to be <= (n+1)*100

    // Establish initial bounds for min_sum based on the first element (i=0)
    // sum_range(a_1, 0, 1) + sum_range(a_2, 0, n)
    // a_1[0] + (a_2[0] + ... + a_2[n-1])
    // The sum is at least 1 + n which is >= n+1
    // The sum is at most 100 + n * 100 which is <= (n+1)*100
    // So the initial min_sum will satisfy the conditions.

    min_sum := calculate_sum(a_1, a_2, n, 0);
    found_an_index := true;

    assert sum_range(a_1, 0, 1) >= 1;
    assert sum_range(a_2, 0, n) >= n;
    assert min_sum >= n + 1 by {
        assert sum_range(a_1, 0, 1) + sum_range(a_2, 0, n) >= 1 + n;
    }
    assert min_sum <= (n + 1) * 100 by {
        assert sum_range(a_1, 0, 1) <= 100;
        assert sum_range(a_2, 0, n) <= n * 100;
        assert sum_range(a_1, 0, 1) + sum_range(a_2, 0, n) <= 100 + n * 100;
    }


    for i := 1 to n - 1
        invariant 0 <= i <= n
        invariant found_an_index ==> min_sum >= n + 1
        invariant found_an_index ==> min_sum <= (n + 1) * 100
        invariant forall k :: 0 <= k < i ==> min_sum <= calculate_sum(a_1, a_2, n, k)
    {
        var current_sum := calculate_sum(a_1, a_2, n, i);

        if current_sum < min_sum {
            min_sum := current_sum;
        }

        // Prove that current_sum satisfies the general bounds
        assert current_sum >= n + 1 by {
            assert sum_range(a_1, 0, i + 1) >= i + 1;
            assert sum_range(a_2, i, n) >= n - i;
            assert sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) >= (i + 1) + (n - i);
            assert sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) >= n + 1;
        }
        assert current_sum <= (n + 1) * 100 by {
            assert sum_range(a_1, 0, i + 1) <= (i + 1) * 100;
            assert sum_range(a_2, i, n) <= (n - i) * 100;
            assert sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) <= (i + 1) * 100 + (n - i) * 100;
            assert sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) <= (i + 1 + n - i) * 100;
            assert sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) <= (n + 1) * 100;
        }
    }

    result := min_sum;
    assert IsValidResult(n, a_1, a_2, result);
}
// </vc-code>

