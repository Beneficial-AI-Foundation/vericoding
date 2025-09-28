use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

// <vc-helpers>

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
    while i < n
        invariant
            1 <= i,
            i <= n,
            result == factorial(i as nat),
        decreases n - i
    {
        result = result * (i + 1);
        proof {
            assert(factorial((i + 1) as nat) == ((i + 1) as nat) * factorial(i as nat));
            assert(result == ((i + 1) as nat) * factorial(i as nat));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}