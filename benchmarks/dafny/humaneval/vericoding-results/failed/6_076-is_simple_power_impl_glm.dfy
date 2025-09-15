// <vc-preamble>
function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fix division by zero by adding requires clause */
function is_divisible_by(n: int, d: nat): bool
    requires d > 0
{
    n % d == 0
}
// </vc-helpers>

// <vc-spec>
method is_simple_power(x: nat, n: int) returns (ans : bool)

    requires x > 0

    ensures ans <==> exists y :: n == power(x, y)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fix logic to correctly determine if n is a power of x */
{
    if n <= 0 {
        ans := false;
    } else if n == 1 {
        ans := true;
    } else if x == 1 {
        ans := n == 1;
    } else {
        var y := 0;
        var current := 1;
        
        while current < n
        invariant current == power(x, y)
        {
            current := current * x;
            y := y + 1;
        }
        
        ans := current == n;
    }
}
// </vc-code>
