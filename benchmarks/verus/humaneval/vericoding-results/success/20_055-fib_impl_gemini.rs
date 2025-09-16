// <vc-preamble>
use vstd::prelude::*;

verus! {

#[verifier::memoize]
spec fn spec_fib(n: nat) -> (ret:nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        1
    } else {
        spec_fib((n - 1) as nat) + spec_fib((n - 2) as nat)
    }
}

spec fn inner_expr_fib(n: u32, ret: Option<u32>) -> (result:bool) {
    match ret {
        None => spec_fib(n as nat) > u32::MAX,
        Some(f) => f == spec_fib(n as nat),
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn spec_fib_is_nondecreasing(i: nat, j: nat)
    requires i <= j
    ensures spec_fib(i) <= spec_fib(j)
    decreases j - i
{
    if i < j {
        spec_fib_is_nondecreasing(i, (j - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn fib(n: u32) -> (ret: Option<u32>)

    ensures
        inner_expr_fib(n, ret),
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return Some(0);
    }

    let mut a: u32 = 0;
    let mut b: u32 = 1;
    let mut i: u32 = 1;

    while i < n
        invariant
            1 <= i <= n,
            a as nat == spec_fib((i - 1) as nat),
            b as nat == spec_fib(i as nat),
            spec_fib(i as nat) <= u32::MAX,
        decreases n - i
    {
        if b > u32::MAX - a {
            proof {
                spec_fib_is_nondecreasing((i + 1) as nat, n as nat);
            }
            return None;
        }

        let next_b = a + b;
        a = b;
        b = next_b;
        i = i + 1;
    }

    Some(b)
}
// </vc-code>

}
fn main() {}