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
    decreases *
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

lemma power_complete(x: nat, n: nat)
    requires x > 1
    requires n > 0
    ensures (exists y :: n == power(x, y)) <==> (exists y :: 0 <= y && n == power(x, y) && (y == 0 || n % x == 0))
{
    if exists y :: n == power(x, y) {
        var y :| n == power(x, y) && y >= 0;
        if y == 0 {
            assert n == 1;
        } else {
            assert n == x * power(x, y-1);
            assert n % x == 0;
        }
    }
}

lemma power_positive(x: nat, y: nat)
    requires x > 0
    ensures power(x, y) >= 1
{
    if y == 0 {
        assert power(x, y) == 1;
    } else {
        power_positive(x, y-1);
        assert power(x, y) == x * power(x, y-1);
        assert power(x, y-1) >= 1;
        assert power(x, y) >= x >= 1;
    }
}

lemma power_one(y: nat)
    ensures power(1, y) == 1
{
    if y == 0 {
        assert power(1, y) == 1;
    } else {
        power_one(y-1);
        assert power(1, y) == 1 * power(1, y-1) == power(1, y-1) == 1;
    }
}

lemma power_strictly_increasing(x: nat, y: nat)
    requires x > 1
    requires y > 0
    ensures power(x, y) > power(x, y-1)
{
    assert power(x, y) == x * power(x, y-1);
    power_positive(x, y-1);
    assert power(x, y-1) >= 1;
    assert power(x, y) >= x * 1 > 1 * power(x, y-1);
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
        power_positive(x, 0);
        assert forall y :: power(x, y) >= 1;
        assert !(exists y :: n == power(x, y));
        return;
    }
    
    if x == 1 {
        ans := (n == 1);
        if n == 1 {
            assert power(x, 0) == 1;
            assert exists y :: n == power(x, y);
        } else {
            power_one(0);
            power_one(1);
            assert forall y :: power(1, y) == 1;
            assert !(exists y :: n == power(x, y));
        }
        return;
    }
    
    var current := 1;
    var y := 0;
    
    while current < n
        invariant current == power(x, y)
        invariant y >= 0
        invariant x > 1
        invariant current >= 1
        invariant forall z :: 0 <= z < y ==> power(x, z) < n
        decreases n - current
    {
        current := current * x;
        y := y + 1;
        
        if current > n {
            ans := false;
            assert forall z :: 0 <= z < y ==> power(x, z) < n;
            assert current == power(x, y) > n;
            if x > 1 {
                assert forall z :: z > y ==> power(x, z) >= power(x, y) > n by {
                    forall z | z > y 
                    ensures power(x, z) >= power(x, y)
                    {
                        power_monotonic(x, y, z);
                    }
                }
            }
            assert !(exists z :: n == power(x, z));
            return;
        }
    }
    
    ans := (current == n);
    if current == n {
        assert n == power(x, y);
        assert exists z :: n == power(x, z);
    } else {
        assert current > n;
        assert forall z :: 0 <= z < y ==> power(x, z) < n;
        assert power(x, y) > n;
        if x > 1 {
            assert forall z :: z > y ==> power(x, z) >= power(x, y) > n by {
                forall z | z > y 
                ensures power(x, z) >= power(x, y)
                {
                    power_monotonic(x, y, z);
                }
            }
        }
        assert !(exists z :: n == power(x, z));
    }
}
// </vc-code>

