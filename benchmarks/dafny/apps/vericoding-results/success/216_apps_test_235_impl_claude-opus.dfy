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
        
        // Prove remaining_after_petya1 >= remaining_after_petya2
        // Note: remaining_after_petya = remaining_after_vasya - remaining_after_vasya/10
        //       = remaining_after_vasya * (1 - 1/10) but in integer arithmetic
        // For integer division: x - x/10 = x * 9 / 10 + (x % 10 * 9) / 10
        // But for our purposes, we just need the inequality
        
        RemainingAfterPetyaMonotone(remaining_after_vasya1, remaining_after_vasya2);
        assert remaining_after_petya1 >= remaining_after_petya2;
        
        // Use monotonicity with respect to first argument
        MonotonicityFirstArgLemma(remaining_after_petya1, remaining_after_petya2, k1);
        assert vasya_eats_with_strategy(remaining_after_petya1, k1) >= vasya_eats_with_strategy(remaining_after_petya2, k1);
        
        // Use monotonicity with respect to second argument
        MonotonicityLemma(remaining_after_petya2, k1, k2);
        assert vasya_eats_with_strategy(remaining_after_petya2, k1) <= vasya_eats_with_strategy(remaining_after_petya2, k2);
        
        // Combine inequalities
        assert cur1 <= cur2;
        assert vasya_eats_with_strategy(remaining_after_petya1, k1) >= vasya_eats_with_strategy(remaining_after_petya2, k1);
        assert vasya_eats_with_strategy(remaining_after_petya2, k1) <= vasya_eats_with_strategy(remaining_after_petya2, k2);
        
        assert vasya_eats_with_strategy(n, k1) == cur1 + vasya_eats_with_strategy(remaining_after_petya1, k1);
        assert vasya_eats_with_strategy(n, k2) == cur2 + vasya_eats_with_strategy(remaining_after_petya2, k2);
        
        // We need to show cur1 + vasya_eats_with_strategy(remaining_after_petya1, k1) <= cur2 + vasya_eats_with_strategy(remaining_after_petya2, k2)
        // We know:
        // - cur1 <= cur2
        // - vasya_eats_with_strategy(remaining_after_petya2, k2) >= vasya_eats_with_strategy(remaining_after_petya2, k1)
        // But we need to relate vasya_eats_with_strategy(remaining_after_petya1, k1) to vasya_eats_with_strategy(remaining_after_petya2, k2)
        
        // The key insight: difference in what's eaten compensates
        DifferenceCompensation(n, k1, k2, cur1, cur2, remaining_after_vasya1, remaining_after_vasya2, 
                             remaining_after_petya1, remaining_after_petya2);
        
        assert vasya_eats_with_strategy(n, k1) <= vasya_eats_with_strategy(n, k2);
    }
}

lemma RemainingAfterPetyaMonotone(x: int, y: int)
    requires x >= y >= 0
    ensures x - x/10 >= y - y/10
{
    // For non-negative integers, if x >= y then x - x/10 >= y - y/10
    // This is because the function f(t) = t - t/10 is monotonically increasing for non-negative t
}

lemma DifferenceCompensation(n: int, k1: int, k2: int, cur1: int, cur2: int,
                            remaining_after_vasya1: int, remaining_after_vasya2: int,
                            remaining_after_petya1: int, remaining_after_petya2: int)
    requires n > 0 && 1 <= k1 <= k2
    requires cur1 == if n < k1 then n else k1
    requires cur2 == if n < k2 then n else k2
    requires remaining_after_vasya1 == n - cur1
    requires remaining_after_vasya2 == n - cur2
    requires remaining_after_petya1 == remaining_after_vasya1 - remaining_after_vasya1 / 10
    requires remaining_after_petya2 == remaining_after_vasya2 - remaining_after_vasya2 / 10
    requires remaining_after_petya1 >= remaining_after_petya2 >= 0
    ensures cur1 + vasya_eats_with_strategy(remaining_after_petya1, k1) <= 
            cur2 + vasya_eats_with_strategy(remaining_after_petya2, k2)
{
    // The extra amount eaten initially: cur2 - cur1 >= 0
    var extra_initial := cur2 - cur1;
    assert extra_initial >= 0;
    
    // The reduction in remaining chocolates
    var reduction := remaining_after_petya1 - remaining_after_petya2;
    assert reduction >= 0;
    
    // Use the bounded difference lemma
    BoundedDifferenceLemma(remaining_after_petya1, remaining_after_petya2, k1);
    assert vasya_eats_with_strategy(remaining_after_petya1, k1) <= 
           vasya_eats_with_strategy(remaining_after_petya2, k1) + reduction;
    
    // Use monotonicity in k
    MonotonicityLemma(remaining_after_petya2, k1, k2);
    assert vasya_eats_with_strategy(remaining_after_petya2, k1) <= 
           vasya_eats_with_strategy(remaining_after_petya2, k2);
    
    // Combine
    assert vasya_eats_with_strategy(remaining_after_petya1, k1) <= 
           vasya_eats_with_strategy(remaining_after_petya2, k2) + reduction;
    
    // Show that extra_initial >= reduction or compensates appropriately
    CompensationRelation(remaining_after_vasya1, remaining_after_vasya2, extra_initial, reduction);
}

lemma BoundedDifferenceLemma(n1: int, n2: int, k: int)
    requires n1 >= n2 >= 0
    requires k >= 1
    ensures vasya_eats_with_strategy(n1, k) <= vasya_eats_with_strategy(n2, k) + (n1 - n2)
    decreases n1
{
    if n2 == 0 {
        VasyaEatsAtMostN(n1, k);
        assert vasya_eats_with_strategy(n1, k) <= n1;
        assert vasya_eats_with_strategy(n2, k) == 0;
        assert vasya_eats_with_strategy(n1, k) <= n1 - n2 + vasya_eats_with_strategy(n2, k);
    } else if n1 == 0 {
        assert false; // Can't happen since n1 >= n2 > 0
    } else {
        var cur1 := if n1 < k then n1 else k;
        var cur2 := if n2 < k then n2 else k;
        
        var remaining_after_vasya1 := n1 - cur1;
        var remaining_after_vasya2 := n2 - cur2;
        
        var remaining_after_petya1 := remaining_after_vasya1 - remaining_after_vasya1 / 10;
        var remaining_after_petya2 := remaining_after_vasya2 - remaining_after_vasya2 / 10;
        
        if n1 < k && n2 < k {
            assert vasya_eats_with_strategy(n1, k) == n1;
            assert vasya_eats_with_strategy(n2, k) == n2;
            assert vasya_eats_with_strategy(n1, k) == vasya_eats_with_strategy(n2, k) + (n1 - n2);
        } else if n1 >= k && n2 >= k {
            assert cur1 == k && cur2 == k;
            RemainingAfterPetyaMonotone(remaining_after_vasya1, remaining_after_vasya2);
            BoundedDifferenceLemma(remaining_after_petya1, remaining_after_petya2, k);
            // The difference contracts by factor of 9/10
            DifferenceContraction(remaining_after_vasya1, remaining_after_vasya2);
            assert remaining_after_petya1 - remaining_after_petya2 <= (remaining_after_vasya1 - remaining_after_vasya2);
            assert remaining_after_vasya1 - remaining_after_vasya2 == n1 - n2;
        } else {
            assert n1 >= k && n2 < k;
            assert cur1 == k && cur2 == n2;
            VasyaEatsAtMostN(remaining_after_petya1, k);
        }
    }
}

lemma CompensationRelation(remaining_after_vasya1: int, remaining_after_vasya2: int, 
                          extra_initial: int, reduction: int)
    requires remaining_after_vasya1 >= remaining_after_vasya2 >= 0
    requires extra_initial == remaining_after_vasya1 - remaining_after_vasya2
    requires reduction == (remaining_after_vasya1 - remaining_after_vasya1/10) - 
                         (remaining_after_vasya2 - remaining_after_vasya2/10)
    ensures extra_initial >= reduction
{
    // reduction = remaining_after_vasya1 - remaining_after_vasya1/10 - remaining_after_vasya2 + remaining_after_vasya2/10
    //           = (remaining_after_vasya1 - remaining_after_vasya2) - (remaining_after_vasya1/10 - remaining_after_vasya2/10)
    //           = extra_initial - (remaining_after_vasya1/10 - remaining_after_vasya2/10)
    // Since remaining_after_vasya1/10 - remaining_after_vasya2/10 >= 0, we have reduction <= extra_initial
}

lemma DifferenceContraction(x: int, y: int)
    requires x >= y >= 0
    ensures (x - x/10) - (y - y/10) <= x - y
{
    // (x - x/10) - (y - y/10) = x - y - (x/10 - y/10) <= x - y
    // because x/10 - y/10 >= 0 when x >= y >= 0
}

lemma MonotonicityFirstArgLemma(n1: int, n2: int, k: int)
    requires n1 >= n2 >= 0
    requires k >= 1
    ensures vasya_eats_with_strategy(n1, k) >= vasya_eats_with_strategy(n2, k)
    decreases n1
{
    if n2 <= 0 {
        assert vasya_eats_with_strategy(n2, k) == 0;
        VasyaEatsNonNegative(n1, k);
        assert vasya_eats_with_strategy(n1, k) >= 0;
    } else if n1 <= 0 {
        assert false; // Can't happen since n1 >= n2 > 0
    } else {
        var cur1 := if n1 < k then n1 else k;
        var cur2 := if n2 < k then n2 else k;
        assert cur1 >= cur2;
        
        var remaining_after_vasya1 := n1 - cur1;
        var remaining_after_vasya2 := n2 - cur2;
        
        var remaining_after_petya1 := remaining_after_vasya1 - remaining_after_vasya1 / 10;
        var remaining_after_petya2 := remaining_after_vasya2 - remaining_after_vasya2 / 10;
        
        if n1 < k && n2 < k {
            assert cur1 == n1 && cur2 == n2;
            assert remaining_after_vasya1 == 0 && remaining_after_vasya2 == 0;
            assert remaining_after_petya1 == 0 && remaining_after_petya2 == 0;
            assert vasya_eats_with_strategy(n1, k) == n1;
            assert vasya_eats_with_strategy(n2, k) == n2;
            assert n1 >= n2;
        } else if n1 >= k && n2 >= k {
            assert cur1 == k && cur2 == k;
            assert remaining_after_vasya1 == n1 - k;
            assert remaining_after_vasya2 == n2 - k;
            assert remaining_after_vasya1 >= remaining_after_vasya2;
            RemainingAfterPetyaMonotone(remaining_after_vasya1, remaining_after_vasya2);
            assert remaining_after_petya1 >= remaining_after_petya2;
            MonotonicityFirstArgLemma(remaining_after_petya1, remaining_after_petya2, k);
        } else {
            assert n1 >= k && n2 < k;
            assert cur1 == k && cur2 == n2;
            assert cur1 >= cur2;
            assert remaining_after_vasya1 == n1 - k;
            assert remaining_after_vasya2 == 0;
            assert remaining_after_petya1 >= 0;
            assert remaining_after_petya2 == 0;
            VasyaEatsNonNegative(remaining_after_petya1, k);
            assert vasya_eats_with_strategy(remaining_after_petya1, k) >= 0;
            assert vasya_eats_with_strategy(remaining_after_petya2, k) == 0;
        }
    }
}

lemma VasyaEatsNonNegative(n: int, k: int)
    requires n >= 0
    requires k >= 1
    ensures vasya_eats_with_strategy(n, k) >= 0
    decreases n
{
    if n <= 0 {
        assert vasya_eats_with_strategy(n, k) == 0;
    } else {
        var cur := if n < k then n else k;
        var remaining_after_vasya := n - cur;
        var remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10;
        assert remaining_after_petya >= 0;
        VasyaEatsNonNegative(remaining_after_petya, k);
        assert vasya_eats_with_strategy(remaining_after_petya, k) >= 0;
        assert vasya_eats_with_strategy(n, k) == cur + vasya_eats_with_strategy(remaining_after_petya, k);
        assert vasya_eats_with_strategy(n, k) >= 0;
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
    VasyaEatsNonNegative(remaining_after_petya, k);
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

