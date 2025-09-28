use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

// <vc-helpers>
proof fn factorial_unfold(n: nat)
    requires n > 0
    ensures factorial(n) == n * factorial((n - 1) as nat)
{
}

proof fn factorial_step(k: nat, result: nat)
    requires k >= 1
    requires result == factorial(k)
    ensures (k + 1) * result == factorial((k + 1) as nat)
{
    factorial_unfold((k + 1) as nat);
}
// </vc-helpers>

// <vc-spec>
fn compute_factorial(n: i32) -> (u: i32)
    requires 1 <= n,
    ensures u == factorial(n as nat),
// </vc-spec>
// <vc-code>
{
    let mut result: i32 = 1;
    let mut i: i32 = 1;
    
    while i <= n
        invariant 
            1 <= i <= n + 1,
            result == factorial((i - 1) as nat),
    {
        proof {
            factorial_step((i - 1) as nat, result as nat);
        }
        result = result * i;
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}