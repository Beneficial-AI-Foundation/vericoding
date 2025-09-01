function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>
lemma power_monotonic(x: nat, y1: nat, y2: nat)
    requires x > 1
    requires y1 < y2
    ensures power(x, y1) < power(x, y2)
{
    if y1 == 0 {
        assert power(x, y1) == 1;
        assert power(x, y2) == x * power(x, y2-1);
        assert power(x, y2-1) >= 1;
        assert power(x, y2) >= x >= 2;
    } else {
        power_monotonic(x, y1-1, y2-1);
        assert power(x, y1-1) < power(x, y2-1);
        assert power(x, y1) == x * power(x, y1-1);
        assert power(x, y2) == x * power(x, y2-1);
    }
}

lemma power_grows_unbounded(x: nat, n: nat)
    requires x > 1
    requires n > 0
    ensures exists y :: power(x, y) > n
{
    var y := n;
    power_monotonic(x, 1, y+1);
    assert power(x, y+1) > power(x, 1) == x;
    if power(x, y+1) > n {
        return;
    } else {
        power_grows_unbounded(x, n + power(x, y+1));
    }
}

lemma power_uniqueness(x: nat, y1: nat, y2: nat)
    requires x > 1
    requires power(x, y1) == power(x, y2)
    ensures y1 == y2
{
    if y1 != y2 {
        if y1 < y2 {
            power_monotonic(x, y1, y2);
            assert power(x, y1) < power(x, y2);
            assert false;
        } else {
            power_monotonic(x, y2, y1);
            assert power(x, y2) < power(x, y1);
            assert false;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method is_simple_power(x: nat, n: int) returns (ans : bool)
    // pre-conditions-start
    requires x > 0
    // pre-conditions-end
    // post-conditions-start
    ensures ans <==> exists y :: n == power(x, y)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if n <= 0 {
        ans := false;
        return;
    }
    
    if x == 1 {
        ans := (n == 1);
        return;
    }
    
    var current := 1;
    var y := 0;
    
    while current < n
        invariant current == power(x, y)
        invariant y >= 0
        invariant forall z :: 0 <= z < y ==> power(x, z) < n
        decreases n - current
    {
        if n % current != 0 || (n / current) % x != 0 {
            ans := false;
            return;
        }
        current := current * x;
        y := y + 1;
    }
    
    ans := (current == n);
}
// </vc-code>

