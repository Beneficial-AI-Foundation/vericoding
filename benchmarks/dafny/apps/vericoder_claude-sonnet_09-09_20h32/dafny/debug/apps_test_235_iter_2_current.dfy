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
lemma VasyaEatsIncreases(n: int, k1: int, k2: int)
    requires n >= 0
    requires k1 >= 1
    requires k2 >= k1
    ensures vasya_eats_with_strategy(n, k1) <= vasya_eats_with_strategy(n, k2)
    decreases n
{
    if n <= 0 {
    } else {
        var cur1 := if n < k1 then n else k1;
        var cur2 := if n < k2 then n else k2;
        var remaining_after_vasya1 := n - cur1;
        var remaining_after_petya1 := remaining_after_vasya1 - remaining_after_vasya1 / 10;
        var remaining_after_vasya2 := n - cur2;
        var remaining_after_petya2 := remaining_after_vasya2 - remaining_after_vasya2 / 10;
        
        assert cur1 <= cur2;
        assert remaining_after_vasya1 >= remaining_after_vasya2;
        assert remaining_after_petya1 >= remaining_after_petya2;
        
        VasyaEatsIncreases(remaining_after_petya1, k1, k2);
        VasyaEatsIncreases(remaining_after_petya2, k1, k2);
    }
}

lemma VasyaEatsPositive(n: int, k: int)
    requires n >= 1
    requires k >= 1
    ensures vasya_eats_with_strategy(n, k) >= 1
    decreases n
{
    if n <= 0 {
    } else {
        var cur := if n < k then n else k;
        var remaining_after_vasya := n - cur;
        var remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10;
        if remaining_after_petya >= 1 {
            VasyaEatsPositive(remaining_after_petya, k);
        }
    }
}

lemma VasyaEatsBounded(n: int, k: int)
    requires n >= 0
    requires k >= 1
    ensures vasya_eats_with_strategy(n, k) <= n
    decreases n
{
    if n <= 0 {
    } else {
        var cur := if n < k then n else k;
        var remaining_after_vasya := n - cur;
        var remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10;
        VasyaEatsBounded(remaining_after_petya, k);
    }
}

lemma VasyaEatsWithLargeK(n: int, k: int)
    requires n >= 1
    requires k >= n
    ensures vasya_eats_with_strategy(n, k) == n
    decreases n
{
    if n <= 0 {
    } else {
        var cur := if n < k then n else k;
        assert cur == n;
        var remaining_after_vasya := n - cur;
        assert remaining_after_vasya == 0;
        var remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10;
        assert remaining_after_petya == 0;
        assert vasya_eats_with_strategy(n, k) == cur + vasya_eats_with_strategy(remaining_after_petya, k);
        assert vasya_eats_with_strategy(remaining_after_petya, k) == 0;
        assert vasya_eats_with_strategy(n, k) == n;
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
    var k := 1;
    while k <= n
        invariant 1 <= k <= n + 1
        invariant k > 1 ==> vasya_eats_with_strategy(n, k - 1) * 2 < n
        decreases n + 1 - k
    {
        if vasya_eats_with_strategy(n, k) * 2 >= n {
            VasyaEatsPositive(n, k);
            VasyaEatsBounded(n, k);
            result := k;
            return;
        }
        VasyaEatsIncreases(n, k, k + 1);
        k := k + 1;
    }
    
    VasyaEatsWithLargeK(n, n);
    assert vasya_eats_with_strategy(n, n) == n;
    assert vasya_eats_with_strategy(n, n) * 2 == 2 * n >= n;
    VasyaEatsPositive(n, n);
    VasyaEatsBounded(n, n);
    result := n;
}
// </vc-code>

