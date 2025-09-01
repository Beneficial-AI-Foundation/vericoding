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
    var y := 1;
    while current_power < n
        invariant current_power > 0
        invariant current_power == power(x, y)
        invariant y >= 1
        decreases n - current_power
    {
        if current_power > n / x { // Prevent overflow
            return false;
        }
        current_power := current_power * x;
        y := y + 1;
    }

    return current_power == n;
}
// </vc-code>

