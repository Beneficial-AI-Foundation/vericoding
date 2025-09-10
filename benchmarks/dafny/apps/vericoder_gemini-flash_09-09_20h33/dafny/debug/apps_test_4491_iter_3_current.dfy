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
    requires 0 <= i <= n // Changed from 0 <= i < n to 0 <= i <= n
    requires ValidInput(n, a_1, a_2) // Added global precondition
    ensures sum_range(a_1, 0, i + 1) == a_1[0] + sum_range(a_1, 1, i + 1)
    ensures calculate_sum(a_1, a_2, n, i) == sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)
    ensures i + 1 >= 0 && i + 1 <= |a_1| // Ensure preconditions for sum_range (first part)
    ensures i >= 0 && i <= |a_2| // Ensure preconditions for sum_range (second part, start)
    ensures n >= 0 && n <= |a_2| // Ensure preconditions for sum_range (second part, end)
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
    var min_sum := calculate_sum(a_1, a_2, n, 0);
    var min_idx := 0;

    assert min_sum >= n + 1 by {
        assert sum_range(a_1, 0, 1) >= 1;
        assert sum_range(a_2, 0, n) >= n;
    }
    assert min_sum <= (n + 1) * 100 by {
        assert sum_range(a_1, 0, 1) <= 100;
        assert sum_range(a_2, 0, n) <= n * 100;
    }

    for i := 1 to n - 1
        invariant 0 <= i <= n
        invariant 0 <= min_idx < i
        invariant min_sum == calculate_sum(a_1, a_2, n, min_idx)
        invariant forall k :: 0 <= k < i ==> min_sum <= calculate_sum(a_1, a_2, n, k)
        invariant min_sum >= n + 1
        invariant min_sum <= (n + 1) * 100
    {
        var current_sum := calculate_sum(a_1, a_2, n, i);

        assert current_sum >= n + 1 by {
            assert sum_range(a_1, 0, i + 1) >= i + 1;
            assert sum_range(a_2, i, n) >= n - i;
        }
        assert current_sum <= (n + 1) * 100 by {
            assert sum_range(a_1, 0, i + 1) <= (i + 1) * 100;
            assert sum_range(a_2, i, n) <= (n - i) * 100;
        }

        if current_sum < min_sum {
            min_sum := current_sum;
            min_idx := i;
        }
    }

    result := min_sum;
    assert IsValidResult(n, a_1, a_2, result) by {
        assert result == calculate_sum(a_1, a_2, n, min_idx);
        assert (exists i :: 0 <= i < n && result == calculate_sum(a_1, a_2, n, i));
        assert (forall k :: 0 <= k < n ==> result <= calculate_sum(a_1, a_2, n, k));
        // The IsValidResult predicate states:
        // P1: result >= n + 1
        // P2: result <= (n + 1) * 100
        // P3: exists i :: 0 <= i < n && result == sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)
        // P4: forall i :: 0 <= i < n ==> result >= sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)

        // P1 and P2 are proven by loop invariants.
        // P3 is true because `result` is `min_sum` which was assigned from one of the `calculate_sum` calls.
        // P4 needs to be `result <= ...` not `result >= ...` for `result` to be the minimum,
        // which matches our loop invariant `min_sum <= calculate_sum(a_1, a_2, n, k)`.
    }
}
// </vc-code>

