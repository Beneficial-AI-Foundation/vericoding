predicate ValidInput(n: int)
{
    n >= 1
}

function vasya_eats_with_strategy(n: int, k: int): int
    requires n >= 0
    requires k >= 1
    decreases n
{
    if n <= 0 then 0
    else
        var cur := if n < k then n else k;
        var remaining_after_vasya := n - cur;
        var remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10;
        cur + vasya_eats_with_strategy(remaining_after_petya, k)
}

predicate IsMinimalSolution(n: int, k: int)
    requires ValidInput(n)
    requires k >= 1
{
    vasya_eats_with_strategy(n, k) * 2 >= n &&
    (k == 1 || vasya_eats_with_strategy(n, k - 1) * 2 < n)
}

// <vc-helpers>
lemma MonotonicK(n: int, k1: int, k2: int)
    requires n >= 0
    requires k1 >= 1
    requires k2 >= 1
    requires k1 <= k2
    ensures vasya_eats_with_strategy(n, k1) <= vasya_eats_with_strategy(n, k2)
    decreases n
{
    if n > 0 {
        var cur1 := if n < k1 then n else k1;
        var cur2 := if n < k2 then n else k2;
        if n < k1 {
            assert cur1 == n;
            assert cur2 == n;
            assert cur1 <= cur2;
        } else {
            assert cur1 == k1;
            assert cur2 == k2;
            assert cur1 <= cur2;
        }
        var remaining_after_vasya := n - cur1;
        var remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10;
        MonotonicK(remaining_after_petya, k1, k2);
    }
}

lemma ExistsMax(n: int)
    requires n >= 1
    ensures vasya_eats_with_strategy(n, n) * 2 >= n
    decreases n
{
    if n > 0 {
        var cur := n;
        var remaining_after_vasya := n - cur;
        var remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10;
        assert remaining_after_vasya == 0;
        assert remaining_after_petya == 0;
        assert vasya_eats_with_strategy(0, n) == 0;
        assert vasya_eats_with_strategy(n, n) == n;
        assert n * 2 >= n;
    }
}

lemma ExistsMin(n: int)
    requires n >= 1
    ensures vasya_eats_with_strategy(n, 1) * 2 >= n
    decreases n
{
    if n == 1 {
        assert vasya_eats_with_strategy(1, 1) == 1;
        assert 1 * 2 >= 1;
    } else {
        var cur := if n < 1 then n else 1;
        assert cur == 1;
        var remaining_after_vasya := n - cur;
        var remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10;
        assert remaining_after_petya < n;
        assert vasya_eats_with_strategy(n, 1) >= 1;
        assert n >= 2;
        assert vasya_eats_with_strategy(n, 1) * 2 >= n;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures 1 <= result <= n
    ensures IsMinimalSolution(n, result)
// </vc-spec>
// <vc-code>
{
    var left := 1;
    var right := n;
    while left < right
        invariant 1 <= left <= right <= n
        invariant vasya_eats_with_strategy(n, right) * 2 >= n
        invariant vasya_eats_with_strategy(n, left - 1) * 2 < n
        decreases right - left
    {
        var mid := (left + right) / 2;
        if vasya_eats_with_strategy(n, mid) * 2 >= n {
            right := mid;
        } else {
            left := mid + 1;
        }
    }
    result := left;
}
// </vc-code>

