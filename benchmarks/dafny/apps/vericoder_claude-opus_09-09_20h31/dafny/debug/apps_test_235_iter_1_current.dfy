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
lemma MonotonicityLemma(n: int, k1: int, k2: int)
    requires n >= 0
    requires 1 <= k1 <= k2
    ensures vasya_eats_with_strategy(n, k1) <= vasya_eats_with_strategy(n, k2)
    decreases n
{
    if n <= 0 {
        // Base case: both return 0
    } else {
        var cur1 := if n < k1 then n else k1;
        var cur2 := if n < k2 then n else k2;
        assert cur1 <= cur2;
        
        var remaining_after_vasya1 := n - cur1;
        var remaining_after_vasya2 := n - cur2;
        assert remaining_after_vasya1 >= remaining_after_vasya2;
        
        var remaining_after_petya1 := remaining_after_vasya1 - remaining_after_vasya1 / 10;
        var remaining_after_petya2 := remaining_after_vasya2 - remaining_after_vasya2 / 10;
        
        // Need to show remaining_after_petya1 >= remaining_after_petya2
        assert remaining_after_vasya1 / 10 >= remaining_after_vasya2 / 10;
        assert remaining_after_petya1 >= remaining_after_petya2;
        
        MonotonicityLemma(remaining_after_petya1, k1, k2);
        MonotonicityLemma(remaining_after_petya2, k1, k2);
        
        assert vasya_eats_with_strategy(remaining_after_petya1, k1) <= vasya_eats_with_strategy(remaining_after_petya1, k2);
        assert vasya_eats_with_strategy(remaining_after_petya2, k1) <= vasya_eats_with_strategy(remaining_after_petya2, k2);
        assert vasya_eats_with_strategy(remaining_after_petya1, k2) >= vasya_eats_with_strategy(remaining_after_petya2, k2);
    }
}

lemma VasyaEatsAtLeastK(n: int, k: int)
    requires n >= k >= 1
    ensures vasya_eats_with_strategy(n, k) >= k
{
    var cur := k;
    assert cur == k;
    var remaining_after_vasya := n - cur;
    var remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10;
    assert remaining_after_petya >= 0;
    assert vasya_eats_with_strategy(remaining_after_petya, k) >= 0;
    assert vasya_eats_with_strategy(n, k) == cur + vasya_eats_with_strategy(remaining_after_petya, k);
    assert vasya_eats_with_strategy(n, k) >= k;
}

lemma VasyaEatsAtMostN(n: int, k: int)
    requires n >= 0
    requires k >= 1
    ensures vasya_eats_with_strategy(n, k) <= n
    decreases n
{
    if n <= 0 {
        assert vasya_eats_with_strategy(n, k) == 0;
    } else {
        var cur := if n < k then n else k;
        var remaining_after_vasya := n - cur;
        var remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10;
        assert remaining_after_petya <= remaining_after_vasya <= n - cur;
        VasyaEatsAtMostN(remaining_after_petya, k);
        assert vasya_eats_with_strategy(remaining_after_petya, k) <= remaining_after_petya;
        assert vasya_eats_with_strategy(n, k) == cur + vasya_eats_with_strategy(remaining_after_petya, k);
        assert vasya_eats_with_strategy(n, k) <= cur + remaining_after_petya;
        assert vasya_eats_with_strategy(n, k) <= n;
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
    
    // vasya_eats_with_strategy(n, n) == n when all chocolates are eaten in first round
    VasyaEatsAtMostN(n, n);
    assert vasya_eats_with_strategy(n, n) <= n;
    
    // When k = n, Vasya eats all n chocolates in the first round
    calc {
        vasya_eats_with_strategy(n, n);
        == {
            assert n >= n;
            var cur := n;
            var remaining_after_vasya := n - cur;
            assert remaining_after_vasya == 0;
            var remaining_after_petya := 0;
            assert vasya_eats_with_strategy(0, n) == 0;
        }
        n;
    }
    
    assert vasya_eats_with_strategy(n, n) * 2 >= n;
    
    // Binary search for the minimal k
    while left < right
        invariant 1 <= left <= right <= n
        invariant vasya_eats_with_strategy(n, right) * 2 >= n
        invariant left == 1 || vasya_eats_with_strategy(n, left - 1) * 2 < n
        decreases right - left
    {
        var mid := (left + right) / 2;
        assert left <= mid <= right;
        
        if mid > 0 && vasya_eats_with_strategy(n, mid) * 2 >= n {
            MonotonicityLemma(n, mid, right);
            right := mid;
        } else {
            if left < n {
                MonotonicityLemma(n, left, mid + 1);
            }
            left := mid + 1;
        }
    }
    
    assert left == right;
    assert vasya_eats_with_strategy(n, left) * 2 >= n;
    assert left == 1 || vasya_eats_with_strategy(n, left - 1) * 2 < n;
    
    result := left;
}
// </vc-code>

