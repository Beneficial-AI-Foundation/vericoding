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
    let mut result = 1;
    let mut i = 1;

    while i <= n
        invariant
            1 <= i <= n + 1,
            result == factorial((i - 1) as nat),
        decreases (n - i) as nat
    {
        result = result * i;
        i = i + 1;
    }

    result
}
// </vc-code>

fn main() {
}

}