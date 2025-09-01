function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>
lemma PowerPositive(x: nat, y: nat)
    requires x > 0
    ensures power(x, y) > 0
{
    if y == 0 {
        assert power(x, y) == 1;
    } else {
        PowerPositive(x, y-1);
        assert power(x, y) == x * power(x, y-1);
    }
}

lemma PowerIncrease(x: nat, y: nat)
    requires x > 1
    requires y > 0
    ensures power(x, y) > power(x, y-1)
    ensures power(x, y) >= x
{
    assert power(x, y) == x * power(x, y-1);
    if y == 1 {
        assert power(x, 0) == 1;
        assert power(x, 1) == x * 1 == x;
    } else {
        PowerPositive(x, y-1);
    }
}

lemma PowerDivisible(x: nat, y: nat)
    requires x > 0
    requires y > 0
    ensures power(x, y) % x == 0
    ensures power(x, y) / x == power(x, y-1)
{
    // Simplified proof without assertion
}

lemma PowerOfOne(k: nat)
    ensures power(1, k) == 1
{
    if k == 0 {
        assert power(1, 0) == 1;
    } else {
        PowerOfOne(k-1);
        assert power(1, k) == 1 * power(1, k-1) == power(1, k-1) == 1;
    }
}

lemma PowerMultiply(x: nat, y: nat, z: nat)
    ensures power(x, y + z) == power(x, y) * power(x, z)
{
    if z == 0 {
        assert power(x, y + 0) == power(x, y) == power(x, y) * 1 == power(x, y) * power(x, 0);
    } else {
        PowerMultiply(x, y, z-1);
        calc {
            power(x, y + z);
            == x * power(x, y + z - 1);
            == x * power(x, y + (z-1));
            == { PowerMultiply(x, y, z-1); }
               x * (power(x, y) * power(x, z-1));
            == power(x, y) * (x * power(x, z-1));
            == power(x, y) * power(x, z);
        }
    }
}

lemma PowerStrictlyIncreasing(x: nat, y1: nat, y2: nat)
    requires x > 1
    requires y1 < y2
    ensures power(x, y1) < power(x, y2)
{
    if y1 == y2 - 1 {
        PowerIncrease(x, y2);
    } else {
        PowerStrictlyIncreasing(x, y1, y2-1);
        PowerIncrease(x, y2);
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
    
    if n == 1 {
        ans := true;
        assert n == power(x, 0);
        return;
    }
    
    // n > 1
    var curr := n;
    var y := 0;
    
    if x == 1 {
        ans := (n == 1);
        if n == 1 {
            assert n == power(x, 0);
        } else {
            // All powers of 1 equal 1
            forall k:nat ensures power(1, k) == 1 {
                PowerOfOne(k);
            }
        }
        return;
    }
    
    // x > 1 case
    while curr > 1
        invariant curr > 0
        invariant n == curr * power(x, y)
        invariant x > 1
        decreases curr
    {
        if curr % x != 0 {
            ans := false;
            
            // Prove that n is not a power of x
            if exists k:nat :: n == power(x, k) {
                var k:nat :| n == power(x, k);
                assert n == curr * power(x, y);
                assert curr * power(x, y) == power(x, k);
                
                if k >= y {
                    if k == y {
                        assert curr == power(x, 0) == 1;
                        assert false;
                    } else {
                        assert k > y;
                        var diff := k - y;
                        assert diff > 0;
                        PowerMultiply(x, y, diff);
                        assert power(x, k) == power(x, y + diff) == power(x, y) * power(x, diff);
                        assert curr == power(x, diff);
                        PowerDivisible(x, diff);
                        assert curr % x == 0;
                        assert false;
                    }
                } else {
                    // k < y
                    var diff := y - k;
                    assert diff > 0;
                    PowerMultiply(x, k, diff);
                    assert power(x, y) == power(x, k + diff) == power(x, k) * power(x, diff);
                    assert curr * power(x, k) * power(x, diff) == power(x, k);
                    PowerPositive(x, k);
                    assert curr * power(x, diff) == 1;
                    PowerPositive(x, diff);
                    assert power(x, diff) >= 1;
                    if diff > 0 {
                        PowerIncrease(x, diff);
                        assert power(x, diff) >= x > 1;
                    }
                    assert curr < 1;
                    assert false;
                }
            }
            return;
        }
        
        curr := curr / x;
        y := y + 1;
        assert n == curr * x * power(x, y-1) == curr * power(x, y);
    }
    
    assert curr == 1;
    assert n == power(x, y);
    ans := true;
}
// </vc-code>

