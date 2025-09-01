function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>
lemma power_properties(x: nat, y: nat)
    requires x > 0
    ensures power(x, y) >= 1
    ensures power(x, y) >= x && y > 0 ==> power(x, y-1) >= 1
{
    if y == 0 {
        calc {
            power(x, 0);
            1;
            >= 1;
        }
    } else {
        calc {
            power(x, y);
            x * power(x, y-1);
            { power_properties(x, y-1); }
            x * (power(x, y-1));
            >= 1 * 1;
            >= 1;
        }
    }
}

lemma power_decreasing(x: nat, k: nat)
    requires x > 1 && k > 0
    ensures power(x, k-1) < power(x, k)
{
    calc {
        power(x, k);
        x * power(x, k-1);
        > 1 * power(x, k-1);
        power(x, k-1);
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
    if x == 1 {
        return n == 1;
    }
    
    if n < 1 {
        return false;
    }
    
    var current := n;
    var y := 0;
    
    while current >= x
        invariant current >= 1
        invariant power(x, y) * current == n
        decreases current
    {
        current := current / x;
        y := y + 1;
    }
    
    return current == 1;
}
// </vc-code>

