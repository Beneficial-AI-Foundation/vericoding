// <vc-preamble>
function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `log_base` helper function is not used in the main code section. Based on compilation error from previous turn, it seems this helper is not correctly integrated or called. Removing it since the main code does not use it. */
// </vc-helpers>

// <vc-spec>
method is_simple_power(x: nat, n: int) returns (ans : bool)

    requires x > 0

    ensures ans <==> exists y :: n == power(x, y)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error `invalid UnaryExpression`. The `n` variable is an `int` so `current_power < n` is valid. The `MaxNat div current_power` is not needed since `n` can be up to `MaxInt` which is `MaxNat` so the current logic does not overflow. The current `while current_power < n` is valid logic as `n` is `int`. */
{
    if n <= 0 then {
        ans := false;
        return;
    }
    if n == 1 then {
        ans := true;
        return;
    }
    if x == 1 then {
        ans := (n == 1);
        return;
    }

    var k: nat := 0;
    var current_power: int := 1;

    while current_power < n
        invariant current_power == power(x, k) as int
        invariant current_power > 0
        invariant k >= 0
        decreases n - current_power
    {
        current_power := current_power * (x as int);
        k := k + 1;
    }

    ans := current_power == n;
}
// </vc-code>
