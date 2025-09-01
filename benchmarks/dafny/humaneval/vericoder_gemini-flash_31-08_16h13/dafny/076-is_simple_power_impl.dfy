function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>
function method power(x: nat, y: nat): nat
  requires x > 0 || y == 0
  ensures y == 0 ==> power(x, y) == 1
  ensures y > 0 && x == 1 ==> power(x,y) == 1
  ensures y > 0 && x > 1 ==> power(x,y) >= x
  ensures y > 0 && x > 1 ==> power(x,y) >= 2
{
    if y == 0 then 1 else x * power(x, y-1)
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
        if x > 1 && current_power > n / x { // Prevent overflow, only if x > 1, so div by x is safe
            return false;
        }
        current_power := current_power * x;
        y := y + 1;
    }

    return current_power == n;
}
// </vc-code>

