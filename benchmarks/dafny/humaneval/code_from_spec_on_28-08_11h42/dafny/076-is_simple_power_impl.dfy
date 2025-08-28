function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>
lemma power_monotonic(x: nat, y1: nat, y2: nat)
    requires x > 1
    requires y1 < y2
    ensures power(x, y1) < power(x, y2)
{
    if y2 == y1 + 1 {
        // Base case
    } else {
        power_monotonic(x, y1, y2 - 1);
    }
}

lemma power_lower_bound(x: nat, y: nat)
    requires x > 1
    requires y > 0
    ensures power(x, y) >= x
{
}

lemma power_grows(x: nat, y: nat)
    requires x > 1
    ensures power(x, y) >= 1
    ensures y > 0 ==> power(x, y) >= x
{
}

lemma power_1_unique(x: nat)
    requires x > 1
    ensures forall y :: power(x, y) == 1 <==> y == 0
{
}

lemma power_1_lemma()
    ensures forall y :: power(1, y) == 1
{
    forall y ensures power(1, y) == 1 {
        if y == 0 {
            assert power(1, 0) == 1;
        } else {
            power_1_lemma_helper(y);
        }
    }
}

lemma power_1_lemma_helper(y: nat)
    requires y > 0
    ensures power(1, y) == 1
{
    if y == 1 {
        assert power(1, 1) == 1 * power(1, 0) == 1 * 1 == 1;
    } else {
        power_1_lemma_helper(y - 1);
        assert power(1, y) == 1 * power(1, y - 1) == 1 * 1 == 1;
    }
}

lemma power_overflow_bound(x: nat, current: nat, n: int)
    requires x > 1
    requires current > 0
    requires current > n / x
    ensures current * x > n
{
    calc {
        current * x;
        >   { assert current > n / x; }
        (n / x) * x;
        >=  { /* integer division property */ }
        n - (x - 1);
        >=  { assert x >= 2; }
        n - x + 1;
    }
    if current * x <= n {
        assert false;
    }
}

lemma power_positive(x: nat, y: nat)
    ensures power(x, y) >= 1
{
    if y == 0 {
        assert power(x, 0) == 1;
    } else {
        power_positive(x, y - 1);
        assert power(x, y) == x * power(x, y - 1) >= x * 1;
        assert x >= 0;
        assert power(x, y) >= 1;
    }
}

lemma power_monotonic_general(x: nat, y1: nat, y2: nat)
    requires x > 1
    requires y1 <= y2
    ensures power(x, y1) <= power(x, y2)
{
    if y1 == y2 {
        assert power(x, y1) == power(x, y2);
    } else {
        power_monotonic(x, y1, y2);
        assert power(x, y1) < power(x, y2);
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
        if n == 1 {
            ans := true;
            assert n == power(x, 0);
        } else {
            ans := false;
            power_positive(x, 0);
            forall y ensures power(x, y) >= 1 {
                power_positive(x, y);
            }
            assert forall y :: power(x, y) >= 1;
            assert n < 1;
            assert forall y :: n != power(x, y);
        }
        return;
    }
    
    if x == 1 {
        ans := n == 1;
        if n == 1 {
            assert n == power(x, 0);
        } else {
            power_1_lemma();
            assert forall y :: power(1, y) == 1;
            assert n != 1;
            assert forall y :: n != power(x, y);
        }
        return;
    }
    
    var current := 1;
    var exp := 0;
    
    while current < n
        invariant current == power(x, exp)
        invariant current > 0
        invariant exp >= 0
        invariant forall i :: 0 <= i < exp ==> power(x, i) < n
        decreases n - current
    {
        if current > (n / x) {
            ans := false;
            power_overflow_bound(x, current, n);
            assert current * x > n;
            assert power(x, exp + 1) == x * current > n;
            forall y: nat | y <= exp ensures power(x, y) < n {
                if y < exp {
                    assert power(x, y) < n;
                } else {
                    assert y == exp;
                    assert power(x, y) == current < n;
                }
            }
            forall y: nat | y > exp ensures power(x, y) > n {
                power_monotonic_general(x, exp + 1, y);
                assert power(x, y) >= power(x, exp + 1) > n;
            }
            assert forall y :: power(x, y) != n;
            return;
        }
        current := current * x;
        exp := exp + 1;
    }
    
    ans := current == n;
    if current == n {
        assert n == power(x, exp);
        assert exists y :: n == power(x, y);
    } else {
        assert current > n;
        assert power(x, exp) > n;
        assert forall i :: 0 <= i < exp ==> power(x, i) < n;
        forall y: nat ensures power(x, y) != n {
            if y < exp {
                assert power(x, y) < n;
            } else {
                power_monotonic_general(x, exp, y);
                assert power(x, y) >= power(x, exp) > n;
            }
        }
        assert forall y :: power(x, y) != n;
    }
}
// </vc-code>
