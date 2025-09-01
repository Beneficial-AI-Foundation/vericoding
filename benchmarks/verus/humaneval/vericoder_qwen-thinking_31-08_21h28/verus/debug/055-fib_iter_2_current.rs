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
// pure-end
// pure-end

spec fn inner_expr_fib(n: u32, ret: Option<u32>) -> (result:bool) {
    match ret {
        None => spec_fib(n as nat) > u32::MAX,
        Some(f) => f == spec_fib(n as nat),
    }
}
// pure-end

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn fib(n: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        inner_expr_fib(n, ret),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        Some(0)
    } else if n == 1 {
        Some(1)
    } else {
        let mut a = 0;
        let mut b = 1;
        for i in 2..=n {
            invariant (a as nat == spec_fib((i - 2) as nat) && b as nat == spec_fib((i - 1) as nat) && a <= u32::MAX && b <= u32::MAX)
            if a > u32::MAX - b {
                return None;
            }
            let c = a + b;
            a = b;
            b = c;
        }
        Some(b)
    }
}
// </vc-code>

} // verus!
fn main() {}