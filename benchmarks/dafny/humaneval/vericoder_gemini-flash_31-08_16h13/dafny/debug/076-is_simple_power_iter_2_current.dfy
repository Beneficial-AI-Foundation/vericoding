function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>

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
    if n == 1 {
        return true;
    }
    if n <= 0 || x == 1 {
        return false;
    }

    var current_power := x;
    while current_power < n
        invariant current_power > 0
        invariant current_power % x == 0
        invariant exists y :: (y == 1 || x > 0) && current_power == power(x, y)
    {
        current_power := current_power * x;
    }

    return current_power == n;
}
// </vc-code>

